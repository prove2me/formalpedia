-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_ne_nil_of_mem_upperOccurrences
-- name    : DeciSigma1.Holes.Fresh.ne_nil_of_mem_upperOccurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:13.237519+00:00
-- url     : https://prove2.me/theorems/1e843932-b18e-4c65-ba5b-752da6db7a7e
-- title:
--   Fresh: ne nil of mem upper Occurrences
-- statement:
--   The word of an upper occurrence is nonempty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L327-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L327-L328

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.ne_nil_of_mem_upperOccurrences {W : Fin k → List α} {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : W o.1 ≠ [] := by sorry
