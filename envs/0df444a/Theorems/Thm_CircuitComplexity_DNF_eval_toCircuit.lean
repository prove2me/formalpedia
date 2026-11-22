-- Prove2me | Theorems.Thm_CircuitComplexity_DNF_eval_toCircuit
-- name    : CircuitComplexity.DNF.eval_toCircuit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:49.558247+00:00
-- url     : https://prove2.me/theorems/be8e8ceb-2519-481a-a6e9-d66f2422b67d
-- title:
--   DNF: eval to Circuit
-- statement:
--   The circuit produced by `toCircuit` correctly computes the DNF formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L209-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L209-L219

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
open CircuitComplexity.DNF

theorem CircuitComplexity.DNF.eval_toCircuit [NeZero N] (φ : DNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by sorry
