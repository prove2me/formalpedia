-- Prove2me | Theorems.Thm_CircuitComplexity_CNF_eval_toCircuit
-- name    : CircuitComplexity.CNF.eval_toCircuit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:46.671564+00:00
-- url     : https://prove2.me/theorems/6593f751-7150-4c15-beb8-79c4411c84a3
-- title:
--   CNF: eval to Circuit
-- statement:
--   The circuit produced by `toCircuit` correctly computes the CNF formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L143-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L143-L153

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
open CircuitComplexity.CNF

theorem CircuitComplexity.CNF.eval_toCircuit [NeZero N] (φ : CNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by sorry
