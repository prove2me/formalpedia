-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts
-- name    : DeciSigma1.Holes.Fresh.crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:46.761796+00:00
-- url     : https://prove2.me/theorems/d498c5a2-8763-4943-b8e2-22c1cd17eb64
-- title:
--   Fresh: cross Boundary Marker Ends subset prefix Occurrence Cuts
-- statement:
--   In every context, the ends of markers that start to the left of `z` lie in the set of
--   lengths of prefixes of `z` that are nonempty suffixes of coordinate words
--   (`prefixOccurrenceCuts W z`, which has at most `k (N - 1)` elements for fresh tuples).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L638-L647
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L638-L647

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
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}

theorem DeciSigma1.Holes.Fresh.crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts {t : ℕ} (u z : List α) :
    crossBoundaryMarkerEnds W t u z ⊆ prefixOccurrenceCuts W z := by sorry
