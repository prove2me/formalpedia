-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperOccurrences_le_start
-- name    : DeciSigma1.Holes.Fresh.upperOccurrences_le_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:44.059997+00:00
-- url     : https://prove2.me/theorems/c5c01bb1-156b-425b-826e-322b297c7211
-- title:
--   Fresh: upper Occurrences le start
-- statement:
--   Upper occurrences of one word are disjoint: an earlier one ends before the next starts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L448-L452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L448-L452

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

theorem DeciSigma1.Holes.Fresh.upperOccurrences_le_start {W : Fin k → List α} {t : ℕ} {o o' : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) (ho' : o' ∈ upperOccurrences W t) (h1 : o.1 = o'.1)
    (h2 : o.2.2 < o'.2.2) : o.2.2 ≤ o'.2.1 := by sorry
