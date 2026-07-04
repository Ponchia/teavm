/*
 *  Copyright 2026 Alexey Andreev.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.teavm.backend.wasm.generate.methods;

import java.util.ArrayList;
import java.util.List;
import org.teavm.backend.wasm.WasmRuntime;
import org.teavm.backend.wasm.generate.WasmGeneratorUtil;
import org.teavm.backend.wasm.generate.classes.WasmGCClassInfoProvider;
import org.teavm.backend.wasm.model.WasmFunction;
import org.teavm.backend.wasm.model.WasmLocal;
import org.teavm.backend.wasm.model.WasmStructure;
import org.teavm.backend.wasm.model.WasmType;
import org.teavm.backend.wasm.model.instruction.WasmCastCondition;
import org.teavm.backend.wasm.model.instruction.WasmFloatBinaryOperation;
import org.teavm.backend.wasm.model.instruction.WasmFloatType;
import org.teavm.backend.wasm.model.instruction.WasmFloatUnaryOperation;
import org.teavm.backend.wasm.model.instruction.WasmInstructionBuilder;
import org.teavm.backend.wasm.model.instruction.WasmInstructionList;
import org.teavm.backend.wasm.model.instruction.WasmInt32Constant;
import org.teavm.backend.wasm.model.instruction.WasmInt64Constant;
import org.teavm.backend.wasm.model.instruction.WasmIntBinaryOperation;
import org.teavm.backend.wasm.model.instruction.WasmIntType;
import org.teavm.backend.wasm.model.instruction.WasmIntUnaryOperation;
import org.teavm.backend.wasm.model.instruction.WasmNullCondition;
import org.teavm.backend.wasm.types.PreciseTypeInference;
import org.teavm.flow.FlowReconstruction;
import org.teavm.flow.FlowTreeNode;
import org.teavm.flow.FlowTreeNodeVisitor;
import org.teavm.model.BasicBlock;
import org.teavm.model.ElementModifier;
import org.teavm.model.InvokeDynamicInstruction;
import org.teavm.model.MethodReference;
import org.teavm.model.Program;
import org.teavm.model.ValueType;
import org.teavm.model.Variable;
import org.teavm.model.instructions.ArrayLengthInstruction;
import org.teavm.model.instructions.AssignInstruction;
import org.teavm.model.instructions.BinaryBranchingInstruction;
import org.teavm.model.instructions.BinaryInstruction;
import org.teavm.model.instructions.BinaryOperation;
import org.teavm.model.instructions.BoundCheckInstruction;
import org.teavm.model.instructions.BranchingInstruction;
import org.teavm.model.instructions.CastInstruction;
import org.teavm.model.instructions.CastIntegerInstruction;
import org.teavm.model.instructions.CastNumberInstruction;
import org.teavm.model.instructions.ClassConstantInstruction;
import org.teavm.model.instructions.CloneArrayInstruction;
import org.teavm.model.instructions.ConstructArrayInstruction;
import org.teavm.model.instructions.ConstructInstruction;
import org.teavm.model.instructions.ConstructMultiArrayInstruction;
import org.teavm.model.instructions.DoubleConstantInstruction;
import org.teavm.model.instructions.EmptyInstruction;
import org.teavm.model.instructions.ExitInstruction;
import org.teavm.model.instructions.FloatConstantInstruction;
import org.teavm.model.instructions.GetElementInstruction;
import org.teavm.model.instructions.GetFieldInstruction;
import org.teavm.model.instructions.InitClassInstruction;
import org.teavm.model.instructions.InstructionVisitor;
import org.teavm.model.instructions.IntegerConstantInstruction;
import org.teavm.model.instructions.InvokeInstruction;
import org.teavm.model.instructions.IsInstanceInstruction;
import org.teavm.model.instructions.JumpInstruction;
import org.teavm.model.instructions.LongConstantInstruction;
import org.teavm.model.instructions.MonitorEnterInstruction;
import org.teavm.model.instructions.MonitorExitInstruction;
import org.teavm.model.instructions.NegateInstruction;
import org.teavm.model.instructions.NullCheckInstruction;
import org.teavm.model.instructions.NullConstantInstruction;
import org.teavm.model.instructions.NumericOperandType;
import org.teavm.model.instructions.PutElementInstruction;
import org.teavm.model.instructions.PutFieldInstruction;
import org.teavm.model.instructions.RaiseInstruction;
import org.teavm.model.instructions.StringConstantInstruction;
import org.teavm.model.instructions.SwitchInstruction;
import org.teavm.model.instructions.UnwrapArrayInstruction;

public class WasmCodeGenerator implements InstructionVisitor, FlowTreeNodeVisitor {
    private FlowReconstruction flowReconstruction = new FlowReconstruction();
    private WasmGCGenerationContext context;
    private WasmInstructionBuilder builder;
    private PreciseTypeInference typeInference;
    private WasmInstructionList[] labels;
    private BasicBlock currentBlock;
    private WasmVariableTracker varTracker;
    private BasicBlock expectedBasicBlock;
    private boolean dontExpectBasicBlock;

    public WasmCodeGenerator(WasmGCGenerationContext context) {
        this.context = context;
    }

    public void generate(Program program, MethodReference currentMethod, WasmFunction function,
            int firstVariable, boolean async) {
        typeInference = new PreciseTypeInference(program, currentMethod, context.hierarchy());
        typeInference.setPhisSkipped(false);
        typeInference.setBackPropagation(true);
        typeInference.ensure();
        for (var i = firstVariable; i < program.variableCount(); ++i) {
            var varType = typeInference.typeOf(i);
            WasmType wasmType;
            if (varType.isArrayUnwrap) {
                var arrayType = context.classInfoProvider().getClassInfo(varType.valueType).getArray();
                wasmType = arrayType.getReference();
            } else {
                wasmType = context.typeMapper().mapType(varType.valueType);
            }
            var local = new WasmLocal(wasmType);
            function.add(local);
        }
        labels = new WasmInstructionList[program.basicBlockCount()];
        var flowRoots = flowReconstruction.reconstruct(program);
        builder = function.getBody().builder();
        varTracker = new WasmVariableTracker(function, firstVariable, builder, program.variableCount());
        for (var root : flowRoots) {
            root.acceptVisitor(this);
        }
        varTracker = null;
        builder = null;
        labels = null;
        typeInference = null;
    }

    @Override
    public void visit(FlowTreeNode.Region node) {
        for (var block : node.blocks) {
            currentBlock = block;
            processBasicBlock(block);
            if (builder.isTerminating()) {
                break;
            }
        }
    }

    @Override
    public void visit(FlowTreeNode.TryCatch node) {

    }

    @Override
    public void visit(FlowTreeNode.Loop node) {
        var outerBuilder = builder;
        builder = builder.loop();
        labels[node.head.getIndex()] = builder.list;
        varTracker.enterLevel(builder);
        for (var part : node.body) {
            part.acceptVisitor(this);
        }
        labels[node.head.getIndex()] = null;
        builder = outerBuilder;
        varTracker.exitLevel();
    }

    @Override
    public void visit(FlowTreeNode.Block node) {
        var outerBuilder = builder;
        builder = builder.block();
        varTracker.enterLevel(builder);
        labels[node.jumpTarget.getIndex()] = builder.list;
        for (var part : node.body) {
            part.acceptVisitor(this);
        }
        labels[node.jumpTarget.getIndex()] = null;
        builder = outerBuilder;
        varTracker.exitLevel();
    }

    private void processBasicBlock(BasicBlock block) {
        assert block == expectedBasicBlock || dontExpectBasicBlock;
        expectedBasicBlock = null;
        dontExpectBasicBlock = false;
        for (var insn : block) {
            builder.setCurrentLocation(insn.getLocation());
            insn.acceptVisitor(this);
            if (builder.isTerminating()) {
                break;
            }
        }
    }

    @Override
    public void visit(EmptyInstruction insn) {
    }

    @Override
    public void visit(ClassConstantInstruction insn) {
        WasmGCGenerationUtil.emitClassLiteral(context.classInfoProvider(), builder, insn.getConstant());
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(NullConstantInstruction insn) {
        var type = typeInference.typeOf(insn.getReceiver());
        var wasmType = context.typeMapper().mapType(type.valueType);
        if (wasmType == WasmType.INT32) {
            builder.i32Const(0);
        } else {
            builder.nullConst((WasmType.Reference) wasmType);
        }
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(IntegerConstantInstruction insn) {
        builder.i32Const(insn.getConstant());
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(LongConstantInstruction insn) {
        builder.i64Const(insn.getConstant());
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(FloatConstantInstruction insn) {
        builder.f32Const(insn.getConstant());
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(DoubleConstantInstruction insn) {
        builder.f64Const(insn.getConstant());
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(StringConstantInstruction insn) {
        var stringConstant = context.strings().getStringConstant(insn.getConstant());
        builder.getGlobal(stringConstant.global);
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(BinaryInstruction insn) {
        varTracker.pushArgs(List.of(insn.getFirstOperand(), insn.getSecondOperand()));
        switch (insn.getOperation()) {
            case COMPARE_GREATER, COMPARE_LESS -> {
                var type = switch (insn.getOperandType()) {
                    case INT -> int.class;
                    case LONG -> long.class;
                    case FLOAT -> float.class;
                    case DOUBLE -> double.class;
                };
                var methodName = "compare";
                if (insn.getOperation() == BinaryOperation.COMPARE_LESS
                        && (insn.getOperandType() == NumericOperandType.FLOAT
                        || insn.getOperandType() == NumericOperandType.DOUBLE)) {
                    methodName = "compareLess";
                }
                var method = new MethodReference(WasmRuntime.class, methodName, type, type, int.class);
                var function = context.functions().forStaticMethod(method);
                builder.call(function);
                varTracker.storeToVariable(insn.getReceiver());
                return;
            }
            case MODULO -> {
                if (insn.getOperandType() == NumericOperandType.FLOAT) {
                    var method = new MethodReference(WasmRuntime.class, "remainder", float.class, float.class,
                            float.class);
                    var function = context.functions().forStaticMethod(method);
                    builder.call(function);
                    varTracker.storeToVariable(insn.getReceiver());
                    return;
                } else if (insn.getOperandType() == NumericOperandType.DOUBLE) {
                    var method = new MethodReference(WasmRuntime.class, "remainder", double.class, double.class,
                            double.class);
                    var function = context.functions().forStaticMethod(method);
                    builder.call(function);
                    varTracker.storeToVariable(insn.getReceiver());
                    return;
                }
            }
            default -> {}
        }
        switch (insn.getOperandType()) {
            case INT, LONG -> {
                var wasmOp = switch (insn.getOperation()) {
                    case ADD -> WasmIntBinaryOperation.ADD;
                    case SUBTRACT -> WasmIntBinaryOperation.SUB;
                    case MULTIPLY -> WasmIntBinaryOperation.MUL;
                    case DIVIDE -> WasmIntBinaryOperation.DIV_SIGNED;
                    case MODULO -> WasmIntBinaryOperation.REM_SIGNED;
                    case AND -> WasmIntBinaryOperation.AND;
                    case OR -> WasmIntBinaryOperation.OR;
                    case XOR -> WasmIntBinaryOperation.XOR;
                    case SHIFT_LEFT -> WasmIntBinaryOperation.SHL;
                    case SHIFT_RIGHT -> WasmIntBinaryOperation.SHR_SIGNED;
                    case SHIFT_RIGHT_UNSIGNED -> WasmIntBinaryOperation.SHR_UNSIGNED;
                    case COMPARE_GREATER, COMPARE_LESS -> null;
                };
                var wasmType = insn.getOperandType() == NumericOperandType.INT ? WasmIntType.INT32 : WasmIntType.INT64;
                builder.intBinary(wasmType, wasmOp);
            }
            case FLOAT, DOUBLE -> {
                var wasmOp = switch (insn.getOperation()) {
                    case ADD -> WasmFloatBinaryOperation.ADD;
                    case SUBTRACT -> WasmFloatBinaryOperation.SUB;
                    case MULTIPLY -> WasmFloatBinaryOperation.MUL;
                    case DIVIDE -> WasmFloatBinaryOperation.DIV;
                    case MODULO,
                         COMPARE_GREATER,
                         COMPARE_LESS,
                         AND,
                         OR,
                         XOR,
                         SHIFT_LEFT,
                         SHIFT_RIGHT,
                         SHIFT_RIGHT_UNSIGNED -> null;
                };
                var wasmType = insn.getOperandType() == NumericOperandType.FLOAT
                        ? WasmFloatType.FLOAT32
                        : WasmFloatType.FLOAT64;
                builder.floatBinary(wasmType, wasmOp);
            }
        }
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(NegateInstruction insn) {
        switch (insn.getOperandType()) {
            case INT -> {
                varTracker.pushArgs(List.of(insn.getOperand()));
                var afterInsn = varTracker.getTargetInstructionAtLevel(1);
                var zero = new WasmInt32Constant(0);
                zero.setLocation(afterInsn.getLocation());
                afterInsn.insertNext(zero);
                builder.intBinary(WasmIntType.INT32, WasmIntBinaryOperation.SUB);
            }
            case LONG -> {
                varTracker.pushArgs(List.of(insn.getOperand()));
                var afterInsn = varTracker.getTargetInstructionAtLevel(1);
                var zero = new WasmInt64Constant(0);
                zero.setLocation(afterInsn.getLocation());
                afterInsn.insertNext(zero);
                builder.intBinary(WasmIntType.INT64, WasmIntBinaryOperation.SUB);
            }
            case FLOAT -> {
                varTracker.pushArgs(List.of(insn.getOperand()));
                builder.floatUnary(WasmFloatType.FLOAT32, WasmFloatUnaryOperation.NEG);
            }
            case DOUBLE -> {
                varTracker.pushArgs(List.of(insn.getOperand()));
                builder.floatUnary(WasmFloatType.FLOAT64, WasmFloatUnaryOperation.NEG);
            }
        }
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(AssignInstruction insn) {
        varTracker.pushArgs(List.of(insn.getReceiver()));
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(CastInstruction insn) {
        if (insn.getTargetType() instanceof ValueType.Object objTarget) {
            var className = objTarget.getClassName();
            if (context.classInfoProvider().getClassInfo(className).isHeapStructure()) {
                return;
            }
        }

        var sourceType = context.typeMapper().mapType(typeInference.typeOf(insn.getValue()).valueType);
        if (!(sourceType instanceof WasmType.Reference sourceRef)) {
            return;
        }

        var targetType = (WasmType.Reference) context.typeMapper().mapType(insn.getTargetType());
        WasmStructure targetStruct = null;
        if (targetType instanceof WasmType.CompositeReference targetTypeRef) {
            var composite = targetTypeRef.composite;
            if (composite instanceof WasmStructure) {
                targetStruct = (WasmStructure) composite;
            }
        }

        var canInsertCast = true;
        if (targetStruct != null && sourceRef instanceof WasmType.CompositeReference sourceComposite) {
            var sourceStruct = sourceComposite.composite instanceof WasmStructure
                    ? (WasmStructure) sourceComposite.composite : null;
            if (sourceStruct != null) {
                if (targetStruct.isSupertypeOf(sourceStruct)) {
                    canInsertCast = false;
                } else if (!sourceStruct.isSupertypeOf(targetStruct)) {
                    generateThrowCce(builder);
                    return;
                }
            }
        }

        if (!insn.isWeak() && context.isStrict()) {
            if (canCastNatively(insn.getTargetType())) {
                if (canInsertCast) {
                    var block = builder.block(context.functionTypes().of(targetType, sourceRef).asBlock());
                    block.castBranch(WasmCastCondition.SUCCESS, sourceRef, targetType, block);
                    generateThrowCce(block);
                }
            } else {
                var objectClass = context.classInfoProvider().getClassInfo("java.lang.Object");
                var vtStruct = objectClass.getVirtualTableStructure();
                varTracker.pushArgs(List.of(insn.getValue()));
                varTracker.ensureVariableInLocal(insn.getValue());
                var block = builder.block(context.functionTypes().of(null, sourceType).asBlock());
                block
                        .nullBranch(WasmNullCondition.NULL, block)
                        .structGet(objectClass.getStructure(), WasmGCClassInfoProvider.VT_FIELD_OFFSET)
                        .structGet(vtStruct, WasmGCClassInfoProvider.CLASS_FIELD_OFFSET);
                WasmGCGenerationUtil.emitClassInfoLiteral(context.classInfoProvider(), block, insn.getTargetType());
                block
                        .call(context.supertypeFunctions().getIsSupertypeFunction(insn.getTargetType()))
                        .branch(block);
                generateThrowCce(block);
                builder
                        .getLocal(varTracker.mapToLocal(insn.getValue()))
                        .cast(targetType);
                if (canInsertCast) {
                    builder.cast(targetType);
                }
            }
        } else if (canInsertCast) {
            builder.cast(targetType);
        }

        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(CastNumberInstruction insn) {
        varTracker.pushArgs(List.of(insn.getValue()));
        builder.nonTrapConvert(WasmGeneratorUtil.mapType(insn.getSourceType()),
                WasmGeneratorUtil.mapType(insn.getTargetType()), true);
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(CastIntegerInstruction insn) {
        varTracker.pushArgs(List.of(insn.getValue()));
        switch (insn.getDirection()) {
            case FROM_INTEGER -> {
                switch (insn.getTargetType()) {
                    case BYTE -> {
                        builder
                                .i32Const(24)
                                .intBinary(WasmIntType.INT32, WasmIntBinaryOperation.SHL)
                                .i32Const(24)
                                .intBinary(WasmIntType.INT32, WasmIntBinaryOperation.SHR_SIGNED);
                    }
                    case SHORT -> {
                        builder
                                .i32Const(16)
                                .intBinary(WasmIntType.INT32, WasmIntBinaryOperation.SHL)
                                .i32Const(16)
                                .intBinary(WasmIntType.INT32, WasmIntBinaryOperation.SHR_SIGNED);
                    }
                    case CHAR -> {
                        builder
                                .i32Const(16)
                                .intBinary(WasmIntType.INT32, WasmIntBinaryOperation.SHL)
                                .i32Const(16)
                                .intBinary(WasmIntType.INT32, WasmIntBinaryOperation.SHR_UNSIGNED);
                    }
                }
            }
            case TO_INTEGER -> {
                // Do nothing
            }
        }
        varTracker.storeToVariable(insn.getReceiver());
    }

    @Override
    public void visit(BranchingInstruction insn) {
        boolean inverted;
        BasicBlock breakTarget;
        BasicBlock continueTarget;
        if (labels[insn.getConsequent().getIndex()] != null) {
            breakTarget = insn.getConsequent();
            continueTarget = insn.getAlternative();
            inverted = false;
        } else {
            assert labels[insn.getAlternative().getIndex()] != null;
            breakTarget = insn.getAlternative();
            continueTarget = insn.getConsequent();
            inverted = true;
        }

        varTracker.pushArgs(List.of(insn.getOperand()));
        switch (insn.getCondition()) {
            case EQUAL -> {
                if (!inverted) {
                    builder.intUnary(WasmIntType.INT32, WasmIntUnaryOperation.EQZ);
                }
            }
            case NOT_EQUAL -> {
                if (inverted) {
                    builder.intUnary(WasmIntType.INT32, WasmIntUnaryOperation.EQZ);
                }
            }
            case LESS -> {
                builder.i32Const(0);
                builder.intBinary(WasmIntType.INT32, !inverted
                        ? WasmIntBinaryOperation.LT_SIGNED
                        : WasmIntBinaryOperation.GE_SIGNED);
            }
            case LESS_OR_EQUAL -> {
                builder.i32Const(0);
                builder.intBinary(WasmIntType.INT32, !inverted
                        ? WasmIntBinaryOperation.LE_SIGNED
                        : WasmIntBinaryOperation.GT_SIGNED);
            }
            case GREATER -> {
                builder.i32Const(0);
                builder.intBinary(WasmIntType.INT32, !inverted
                        ? WasmIntBinaryOperation.GT_SIGNED
                        : WasmIntBinaryOperation.LE_SIGNED);
            }
            case GREATER_OR_EQUAL -> {
                builder.i32Const(0);
                builder.intBinary(WasmIntType.INT32, !inverted
                        ? WasmIntBinaryOperation.GE_SIGNED
                        : WasmIntBinaryOperation.LT_SIGNED);
            }
            case NULL -> {
                builder.isNull();
                if (inverted) {
                    builder.intUnary(WasmIntType.INT32, WasmIntUnaryOperation.EQZ);
                }
            }
            case NOT_NULL -> {
                builder.isNull();
                if (!inverted) {
                    builder.intUnary(WasmIntType.INT32, WasmIntUnaryOperation.EQZ);
                }
            }
        }

        branchEither(breakTarget, continueTarget);
    }

    @Override
    public void visit(BinaryBranchingInstruction insn) {
        boolean inverted;
        BasicBlock breakTarget;
        BasicBlock continueTarget;
        if (labels[insn.getConsequent().getIndex()] != null) {
            breakTarget = insn.getConsequent();
            continueTarget = insn.getAlternative();
            inverted = false;
        } else {
            assert labels[insn.getAlternative().getIndex()] != null;
            breakTarget = insn.getAlternative();
            continueTarget = insn.getConsequent();
            inverted = true;
        }

        varTracker.pushArgs(List.of(insn.getFirstOperand(), insn.getSecondOperand()));
        switch (insn.getCondition()) {
            case EQUAL -> {
                builder.intBinary(WasmIntType.INT32, !inverted
                        ? WasmIntBinaryOperation.EQ
                        : WasmIntBinaryOperation.SUB);
            }
            case NOT_EQUAL -> {
                builder.intBinary(WasmIntType.INT32, !inverted
                        ? WasmIntBinaryOperation.SUB
                        : WasmIntBinaryOperation.EQ);
            }
            case REFERENCE_EQUAL -> {
                builder.refEqual();
                if (inverted) {
                    builder.intUnary(WasmIntType.INT32, WasmIntUnaryOperation.EQZ);
                }
            }
            case REFERENCE_NOT_EQUAL -> {
                builder.refEqual();
                if (!inverted) {
                    builder.intUnary(WasmIntType.INT32, WasmIntUnaryOperation.EQZ);
                }
            }
        }

        branchEither(breakTarget, continueTarget);
    }

    private void branchEither(BasicBlock breakTarget, BasicBlock continueTarget) {
        if (varTracker.hasStack() || !extractPhiArgs(breakTarget).isEmpty()) {
            var ifInsn = builder.conditional();
            var condBuilder = ifInsn.getThenBlock().builder();
            varTracker.enterLevel(condBuilder);
            insertPhis(condBuilder, breakTarget);
            condBuilder.branch(labels[breakTarget.getIndex()]);
            varTracker.exitLevel();
            insertPhis(builder, continueTarget);
        } else{
            builder.branch(labels[breakTarget.getIndex()]);
        }
    }

    @Override
    public void visit(JumpInstruction insn) {
        insertPhis(builder, insn.getTarget());
        varTracker.dropStack();
        var label = labels[insn.getTarget().getIndex()];
        if (label != null) {
            builder.breakTo(label);
        } else {
            assert expectedBasicBlock == null && !dontExpectBasicBlock;
            expectedBasicBlock = insn.getTarget();
        }
    }

    private void insertPhis(WasmInstructionBuilder builder, BasicBlock target) {
        varTracker.pushArgs(extractPhiArgs(target));
        readPhis(builder, target);
    }

    private void readPhis(WasmInstructionBuilder builder, BasicBlock target) {
        var phis = target.getPhis();
        for (var i = phis.size() - 1; i >= 0; --i) {
            builder.getLocal(varTracker.mapToLocal(phis.get(i).getReceiver()));
        }
    }

    @Override
    public void visit(SwitchInstruction insn) {

    }

    @Override
    public void visit(ExitInstruction insn) {
        assert !dontExpectBasicBlock && expectedBasicBlock == null;
        dontExpectBasicBlock = true;
        if (insn.getValueToReturn() != null) {
            varTracker.pushArgs(List.of(insn.getValueToReturn()));
        }
        builder.return_();
    }

    @Override
    public void visit(RaiseInstruction insn) {
        assert !dontExpectBasicBlock && expectedBasicBlock == null;
        dontExpectBasicBlock = true;
        varTracker.pushArgs(List.of(insn.getException()));
        builder.throw_(context.getExceptionTag());
    }

    @Override
    public void visit(ConstructArrayInstruction insn) {

    }

    @Override
    public void visit(ConstructInstruction insn) {

    }

    @Override
    public void visit(ConstructMultiArrayInstruction insn) {

    }

    @Override
    public void visit(GetFieldInstruction insn) {

    }

    @Override
    public void visit(PutFieldInstruction insn) {

    }

    @Override
    public void visit(ArrayLengthInstruction insn) {

    }

    @Override
    public void visit(CloneArrayInstruction insn) {

    }

    @Override
    public void visit(UnwrapArrayInstruction insn) {

    }

    @Override
    public void visit(GetElementInstruction insn) {

    }

    @Override
    public void visit(PutElementInstruction insn) {

    }

    @Override
    public void visit(InvokeInstruction insn) {

    }

    @Override
    public void visit(InvokeDynamicInstruction insn) {

    }

    @Override
    public void visit(IsInstanceInstruction insn) {

    }

    @Override
    public void visit(InitClassInstruction insn) {

    }

    @Override
    public void visit(NullCheckInstruction insn) {

    }

    @Override
    public void visit(MonitorEnterInstruction insn) {

    }

    @Override
    public void visit(MonitorExitInstruction insn) {

    }

    @Override
    public void visit(BoundCheckInstruction insn) {

    }

    private boolean canCastNatively(ValueType type) {
        if (type instanceof ValueType.Array) {
            // arrays with non-primitive item types all share the Array<java.lang.Object>
            // structure, so ref.test can only distinguish primitive arrays and Object[]
            // itself; other item types need a class check
            var itemType = ((ValueType.Array) type).getItemType();
            return itemType instanceof ValueType.Primitive
                    || itemType.equals(ValueType.object("java.lang.Object"));
        }
        if (!(type instanceof ValueType.Object)) {
            return false;
        }
        var className = ((ValueType.Object) type).getClassName();
        var cls = context.classes().get(className);
        if (cls == null) {
            return false;
        }
        return !cls.hasModifier(ElementModifier.INTERFACE);
    }

    private void generateThrowCce(WasmInstructionBuilder target) {
        target.call(context.cceMethod());
        target.throw_(context.getExceptionTag());
    }

    private List<Variable> extractPhiArgs(BasicBlock target) {
        var phiArgs = new ArrayList<Variable>();
        for (var phi : target.getPhis()) {
            for (var incoming : phi.getIncomings()) {
                if (incoming.getSource() == currentBlock) {
                    phiArgs.add(incoming.getValue());
                }
            }
        }
        return phiArgs;
    }
}
