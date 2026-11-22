-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_target_piece_of_junction
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.target_piece_of_junction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:46:55.732393+00:00
-- url     : https://prove2.me/theorems/76cfa736-9990-42e2-a958-89b79b9f2f53
-- title:
--   Admissible Deletion: target piece of junction
-- statement:
--   The junction of a shortened host piece that starts strictly inside the compared window gives a
--   piece of the class in the target at the corresponding cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L345-L364
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L345-L364

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.target_piece_of_junction (hN : 0 < N) {i j : Fin k} {ct ch : ℕ}
    (hcmp : SuffixComparison (editedTuple W ρ N x j) ct (editedTuple W ρ N x i) ch)
        (R : Piece W ρ.length)
    (hRl : R.coordinate = i) (hxR : x R ≠ 0) (h1 : ch < (hx.imagePiece R).start)
    (h2 : (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < ch +
        ((editedTuple W ρ N x j).length - ct)) :
    ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧ P' ∈
        piecesOf (editedTuple W ρ N x) ρ ∧
      P'.start = ct + ((hx.imagePiece R).start - ch) := by sorry
