-- Prove2me | Theorems.Thm_CircuitComplexity_AONOp_eval_two_and
-- name    : CircuitComplexity.AONOp.eval_two_and
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:39.010958+00:00
-- url     : https://prove2.me/theorems/7e208399-ff81-43c2-87d4-2ded667510cc
-- title:
--   AONOp: eval two and
-- statement:
--   A fan-in-2 AND gate computes the conjunction of its two inputs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AON/Defs.lean#L70-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/AON/Defs.lean#L70-L72

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.AONOp.eval_two_and (inputs : BitString 2) :
    AONOp.eval .and 2 inputs = (inputs 0 && inputs 1) := by sorry
