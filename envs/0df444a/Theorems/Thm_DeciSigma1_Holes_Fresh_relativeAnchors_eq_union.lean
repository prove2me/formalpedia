-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_relativeAnchors_eq_union
-- name    : DeciSigma1.Holes.Fresh.relativeAnchors_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:20.514921+00:00
-- url     : https://prove2.me/theorems/60f25c62-635e-41b9-8df8-acc05af518a8
-- title:
--   Fresh: relative Anchors eq union
-- statement:
--   The anchors of a text in a context, at every level: at level `0` all cuts are anchors of
--   the text alone.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L282-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L282-L290

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.relativeAnchors_eq_union {W : Fin k → List α} (t : ℕ) (u z : List α) :
    relativeAnchors W t u z = contextAnchors W t z ∪ crossBoundaryMarkerEnds W t u z := by sorry
