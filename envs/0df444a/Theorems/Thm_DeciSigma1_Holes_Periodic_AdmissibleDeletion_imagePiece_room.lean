-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_room
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_room
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:00.621958+00:00
-- url     : https://prove2.me/theorems/ed231daa-c777-4697-b0af-18ee0761085e
-- title:
--   Admissible Deletion: image Piece room
-- statement:
--   The Admissible Deletion construction uses the image Piece room property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L320-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L320-L324

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_room {R : Piece W ρ.length} (hxR : x R ≠ 0) :
    (hx.imagePiece R).start + 6 * Periodic.boundaryMargin N ρ.length + 2 *
        Periodic.statePeriodModulus N ρ.length ≤ (hx.imagePiece R).stop := by sorry
