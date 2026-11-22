-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_piece_mem
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_piece_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:44:37.987816+00:00
-- url     : https://prove2.me/theorems/d388eb6d-9bc1-4578-915e-65ecf15506e1
-- title:
--   Admissible Deletion: image Piece piece mem
-- statement:
--   The Admissible Deletion construction uses the image Piece piece mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L316-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L316-L318

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_piece_mem {R : Piece W ρ.length} (hxR : x R ≠ 0) :
    hx.imagePiece R ∈ piecesOf (editedTuple W ρ N x) ρ := by sorry
