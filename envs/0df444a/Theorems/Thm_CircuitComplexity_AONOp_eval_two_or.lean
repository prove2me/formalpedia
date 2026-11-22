-- Prove2me | Theorems.Thm_CircuitComplexity_AONOp_eval_two_or
-- name    : CircuitComplexity.AONOp.eval_two_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:37.361508+00:00
-- url     : https://prove2.me/theorems/fbe36d70-9579-493b-a2a0-1b99e1801b46
-- title:
--   AONOp: eval two or
-- statement:
--   A fan-in-2 OR gate computes the disjunction of its two inputs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AON/Defs.lean#L75-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AON/Defs.lean#L75-L77

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.AONOp.eval_two_or (inputs : BitString 2) :
    AONOp.eval .or 2 inputs = (inputs 0 || inputs 1) := by sorry
