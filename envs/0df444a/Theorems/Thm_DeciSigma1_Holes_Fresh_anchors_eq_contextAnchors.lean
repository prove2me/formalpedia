-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_eq_contextAnchors
-- name    : DeciSigma1.Holes.Fresh.anchors_eq_contextAnchors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:42.805808+00:00
-- url     : https://prove2.me/theorems/b8d05c3b-1781-4898-bd4c-878701cd256e
-- title:
--   Fresh: anchors eq context Anchors
-- statement:
--   For an active coordinate, the end of its word is a context anchor, so its anchors are its
--   context anchors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L271-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L271-L278

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

theorem DeciSigma1.Holes.Fresh.anchors_eq_contextAnchors {W : Fin k → List α} {t : ℕ} {l : Fin k}
    (hl : l ∈ active W t) : anchors W t l = contextAnchors W t (W l) := by sorry
