-- Prove2me | Theorems.Thm_CircuitComplexity_full_term_unique
-- name    : CircuitComplexity.full_term_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:20.6488+00:00
-- url     : https://prove2.me/theorems/881a5f4a-f31e-404d-99e7-2fb97860443b
-- title:
--   Circuit Complexity: full term unique
-- statement:
--   If a term mentions all N variables, it is satisfied by at most one assignment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L275-L287
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L275-L287

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

theorem CircuitComplexity.full_term_unique {term : List (Literal N)}
    (hfull : ∀ i : Fin N, ∃ l ∈ term, l.var = i)
    {x y : BitString N}
    (hx : term.all (fun l => l.eval x) = true)
    (hy : term.all (fun l => l.eval y) = true) :
    x = y := by sorry
