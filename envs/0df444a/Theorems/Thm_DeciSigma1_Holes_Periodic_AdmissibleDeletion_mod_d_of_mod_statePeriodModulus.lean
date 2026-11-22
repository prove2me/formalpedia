-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_mod_d_of_mod_statePeriodModulus
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.mod_d_of_mod_statePeriodModulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:25.298322+00:00
-- url     : https://prove2.me/theorems/d6d8db1e-ce90-4e9d-a71b-64e85ff72a81
-- title:
--   Admissible Deletion: mod d of mod state Period Modulus
-- statement:
--   The Admissible Deletion construction uses the mod d of mod state Period Modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L538-L543
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L538-L543

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
omit hx
omit [DecidableEq α]

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.mod_d_of_mod_statePeriodModulus {a b : ℕ} (h : SameStatePhase N ρ.length a b) :
    a % ρ.length = b % ρ.length := by sorry
