-- Prove2me | Theorems.Thm_CircuitComplexity_AONFor_is_Correct
-- name    : CircuitComplexity.AONFor_is_Correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:14.980389+00:00
-- url     : https://prove2.me/theorems/464a905f-599a-40f2-929c-f79f92f2b110
-- title:
--   Circuit Complexity: AONFor is Correct
-- statement:
--   The single-output DNF circuit correctly computes `f`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/AON.lean#L187-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/AON.lean#L187-L223

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.AONFor_is_Correct {N : Nat} [NeZero N] (f : BitString N → Bool) :
    (fun (x : BitString 1) => x 0) ∘ (AONFor f).eval = f := by sorry
