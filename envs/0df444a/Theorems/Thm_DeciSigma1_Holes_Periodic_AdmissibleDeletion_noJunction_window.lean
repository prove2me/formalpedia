-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_noJunction_window
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.noJunction_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:44:57.737734+00:00
-- url     : https://prove2.me/theorems/13a5b87e-f432-4bdb-ae2e-b58f06ebcd66
-- title:
--   Admissible Deletion: no Junction window
-- statement:
--   No junction of word `l` lies in the window `(c', c' + n)` if `n ≤ m`, the shortened pieces
--   starting at or before `c'` have no junction in `(c', c' + m)`, and the pieces starting after `c'`
--   have no junction in `(c', c' + n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L391-L401
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L391-L401

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.noJunction_window {l : Fin k} {c' m n : ℕ} (hNJ : hx.NoInteriorJunction l c' m)
    (hn : n ≤ m)
    (hafter : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 → c' < (hx.imagePiece R).start →
      (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n → False) :
    ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n) := by sorry
