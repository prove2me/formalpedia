-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_keepCut_of_mem
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.keepCut_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:45:44.572257+00:00
-- url     : https://prove2.me/theorems/036f421a-3f7a-426d-9119-8ab7c49a47f4
-- title:
--   Admissible Deletion: keep Cut of mem
-- statement:
--   The image of a deleted position is the junction of a shortened piece.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L614-L624
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L614-L624

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.keepCut_of_mem {l : Fin k} {p : ℕ} (hp : p ∈ deletedPositions W ρ N x l) :
    ∃ R : Piece W ρ.length, R.coordinate = l ∧ x R ≠ 0 ∧
      retainedCount (deletedPositions W ρ N x l) p =
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length := by sorry
