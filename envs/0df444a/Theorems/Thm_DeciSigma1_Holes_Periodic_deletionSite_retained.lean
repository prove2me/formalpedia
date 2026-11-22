-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_deletionSite_retained
-- name    : DeciSigma1.Holes.Periodic.deletionSite_retained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:42.279856+00:00
-- url     : https://prove2.me/theorems/d5b0fde0-1e0b-40fd-b3f8-17889f4d1590
-- title:
--   Periodic: deletion Site retained
-- statement:
--   No position of a piece `R` of another class, with period at most `|ρ|` and length at least
--   `|ρ|` plus its period, is deleted, and neither are the letters just before and after it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L887-L902
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L887-L902

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

theorem DeciSigma1.Holes.Periodic.deletionSite_retained (hN : 0 < N) (R : Piece W dR)
    (hcls : ¬ IsConjugate R.root ρ) (hd : dR ≤ ρ.length)
    (hlen : ρ.length + dR ≤ R.len) {p : ℕ}
    (hp : R.start ≤ p + 1) (hpe : p ≤ R.stop) : p ∉ deletedPositions W ρ N x R.coordinate := by sorry
