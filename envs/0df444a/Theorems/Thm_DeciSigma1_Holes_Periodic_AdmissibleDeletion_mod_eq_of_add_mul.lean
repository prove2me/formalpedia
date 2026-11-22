-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_mod_eq_of_add_mul
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.mod_eq_of_add_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:22.333083+00:00
-- url     : https://prove2.me/theorems/907b9fa3-68a7-4f7a-88fd-f526667adabe
-- title:
--   Admissible Deletion: mod eq of add mul
-- statement:
--   The Admissible Deletion construction uses the mod eq of add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L531-L534
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L531-L534

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
omit [DecidableEq α] hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.mod_eq_of_add_mul {a b u v M : ℕ} (h : a + M * u = b + M * v) : a % M = b % M := by sorry
