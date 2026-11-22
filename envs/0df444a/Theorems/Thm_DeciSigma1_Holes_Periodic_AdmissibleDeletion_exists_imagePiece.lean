-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_exists_imagePiece
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.exists_imagePiece
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:56.23487+00:00
-- url     : https://prove2.me/theorems/82700b0e-2270-4cae-85ab-feb0963feee1
-- title:
--   Admissible Deletion: exists image Piece
-- statement:
--   Every piece of the edited tuple is the image of a piece.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L681-L799
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L681-L799

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.exists_imagePiece (P' : Piece (editedTuple W ρ N x) ρ.length) :
    ∃ P : Piece W ρ.length, hx.imagePiece P = P' := by sorry
