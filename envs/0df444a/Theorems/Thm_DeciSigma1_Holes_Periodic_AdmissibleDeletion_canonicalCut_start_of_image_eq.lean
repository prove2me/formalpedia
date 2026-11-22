-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_start_of_image_eq
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_start_of_image_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:07.061296+00:00
-- url     : https://prove2.me/theorems/e2509a44-8ad2-4348-85cb-ca1d2a6fe7e4
-- title:
--   Admissible Deletion: canonical Cut start of image eq
-- statement:
--   The Admissible Deletion construction uses the canonical Cut start of image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L372-L378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L372-L378

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_start_of_image_eq {P : Piece W ρ.length}
    {P' : Piece (editedTuple W ρ N x) ρ.length}
    (hP : hx.imagePiece P = P') {l : Fin k}
        (hl : P'.coordinate = l) :
            CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l P.start P'.start := by sorry
