-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_exists_preserved_piece_of_nonconjugate_root
-- name    : DeciSigma1.Holes.Periodic.exists_preserved_piece_of_nonconjugate_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:48.07885+00:00
-- url     : https://prove2.me/theorems/54705b52-f549-4cfb-9280-1672e348b6b6
-- title:
--   Periodic: exists preserved piece of nonconjugate root
-- statement:
--   A piece `R` of another class, with period at most `|ρ|` and length at least `|ρ|` plus its
--   period, survives the deletion: none of its positions and none of the adjacent letters that
--   end it is deleted, and the edited tuple has a piece with the same coordinate, length and
--   root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L908-L932
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L908-L932

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
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
variable {N dR : ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx

theorem DeciSigma1.Holes.Periodic.exists_preserved_piece_of_nonconjugate_root (hN : 0 < N) (R : Piece W dR)
    (hcls : ¬ IsConjugate R.root ρ) (hd : dR ≤ ρ.length)
    (hlen : ρ.length + dR ≤ R.len) :
    (∀ p, R.start ≤ p → p < R.stop → p ∉ deletedPositions W ρ N x R.coordinate) ∧
    (R.start ≠ 0 → R.start - 1 ∉ deletedPositions W ρ N x R.coordinate) ∧
    (R.stop < (W R.coordinate).length → R.stop ∉ deletedPositions W ρ N x R.coordinate) ∧
    ∃ R' : Piece (editedTuple W ρ N x) dR,
      R'.coordinate = R.coordinate ∧ R'.len = R.len ∧ R'.root = R.root := by sorry
