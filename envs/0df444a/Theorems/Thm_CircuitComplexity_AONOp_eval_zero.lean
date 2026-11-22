-- Prove2me | Theorems.Thm_CircuitComplexity_AONOp_eval_zero
-- name    : CircuitComplexity.AONOp.eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:40.761817+00:00
-- url     : https://prove2.me/theorems/64cf95f5-ea2f-4945-8c3d-52c233bcde45
-- title:
--   AONOp: eval zero
-- statement:
--   `eval` on 0 inputs gives the identity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L84-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean#L84-L85

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.AONOp.eval_zero (op : AONOp) : op.eval 0 Fin.elim0 = op.identity := by sorry
