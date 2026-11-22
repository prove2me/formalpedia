-- Prove2me | Theorems.Thm_CircuitComplexity_AONOp_binOp_assoc
-- name    : CircuitComplexity.AONOp.binOp_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:37.618485+00:00
-- url     : https://prove2.me/theorems/7c14297e-d1df-413e-91ea-fe2c16721996
-- title:
--   AONOp: bin Op assoc
-- statement:
--   The AONOp construction uses the bin Op assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L66-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L66-L68

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.AONOp.binOp_assoc (op : AONOp) (a b c : Bool) :
    op.binOp (op.binOp a b) c = op.binOp a (op.binOp b c) := by sorry
