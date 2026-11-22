-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop_eq_length_iff
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop_eq_length_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:24.447846+00:00
-- url     : https://prove2.me/theorems/8e65a08e-50eb-4776-8502-73d2e318f887
-- title:
--   Admissible Deletion: image Piece stop eq length iff
-- statement:
--   The Admissible Deletion construction uses the image Piece stop eq length iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L585-L594
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L585-L594

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop_eq_length_iff (P : Piece W ρ.length) :
    (hx.imagePiece P).stop = (editedTuple W ρ N x P.coordinate).length ↔ P.stop =
        (W P.coordinate).length := by sorry
