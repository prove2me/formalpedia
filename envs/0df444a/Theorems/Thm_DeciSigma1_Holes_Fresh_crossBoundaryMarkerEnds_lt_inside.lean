-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_crossBoundaryMarkerEnds_lt_inside
-- name    : DeciSigma1.Holes.Fresh.crossBoundaryMarkerEnds_lt_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:26.150467+00:00
-- url     : https://prove2.me/theorems/9dd63711-e612-42be-8f9e-b7ec96567aad
-- title:
--   Fresh: cross Boundary Marker Ends lt inside
-- statement:
--   The ends of markers that start to the left of `z` lie strictly before every anchor of `z` alone
--   (at level `0` there are no such ends).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L294-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L294-L300

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

theorem DeciSigma1.Holes.Fresh.crossBoundaryMarkerEnds_lt_inside {W : Fin k → List α} {t : ℕ} {u z : List α}
    {p q : ℕ} (hp : p ∈ crossBoundaryMarkerEnds W t u z) (hq : q ∈ contextAnchors W t z) : p <
        q := by sorry
