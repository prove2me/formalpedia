-- Prove2me | Theorems.Thm_CircuitComplexity_AONOp_eval_one
-- name    : CircuitComplexity.AONOp.eval_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:40.572805+00:00
-- url     : https://prove2.me/theorems/c921342e-75b6-4df3-9f3a-32c0dc333dfd
-- title:
--   AONOp: eval one
-- statement:
--   `eval` on 1 input gives `identity op input`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L88-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L88-L90

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.AONOp.eval_one (op : AONOp) (v : Fin 1 → Bool) :
    op.eval 1 v = op.binOp op.identity (v 0) := by sorry
