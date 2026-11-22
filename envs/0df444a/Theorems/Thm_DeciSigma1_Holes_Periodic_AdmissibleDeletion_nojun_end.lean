-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_nojun_end
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.nojun_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:44:48.687467+00:00
-- url     : https://prove2.me/theorems/2e8a94f2-e0f8-4acc-ac93-66d822e91375
-- title:
--   Admissible Deletion: nojun end
-- statement:
--   For a piece of the edited tuple, `NoInteriorJunction` holds at the cut `|ρ|` letters before its
--   end, for every window length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L328-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L328-L341

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.nojun_end (P' : Piece (editedTuple W ρ N x) ρ.length) (m : ℕ) :
    hx.NoInteriorJunction P'.coordinate (P'.stop - ρ.length) m := by sorry
