-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_relativeAnchors_eq
-- name    : DeciSigma1.Holes.Fresh.relativeAnchors_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:42.249871+00:00
-- url     : https://prove2.me/theorems/4c0ddcec-4250-4ac4-95f2-19d6ac883c5b
-- title:
--   Fresh: relative Anchors eq
-- statement:
--   In any context, the lower anchors of `z` are the anchors of `z` alone, which do not depend
--   on the context, and the ends of markers that start to the left of `z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L596-L613
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L596-L613

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

theorem DeciSigma1.Holes.Fresh.relativeAnchors_eq {t : ℕ} (ht : 1 ≤ t) (u z : List α) :
    relativeAnchors W t u z = contextAnchors W t z ∪ crossBoundaryMarkerEnds W t u z := by sorry
