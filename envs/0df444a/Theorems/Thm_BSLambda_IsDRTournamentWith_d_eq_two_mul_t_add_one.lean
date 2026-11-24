-- Prove2me | Theorems.Thm_BSLambda_IsDRTournamentWith_d_eq_two_mul_t_add_one
-- name    : BSLambda.IsDRTournamentWith.d_eq_two_mul_t_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:25.113606+00:00
-- url     : https://prove2.me/theorems/3ed25cfe-603e-401b-83e8-eec907ef8fb9
-- title:
--   Is DRTournament With: d eq two mul t add one
-- statement:
--   A doubly regular tournament with at least two vertices satisfies `d = 2 * t + 1`; in
--   particular `d - 1 - t = t`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L232-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L232-L250

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
open BSLambda.IsDRTournamentWith
variable {Arc : ι → ι → Bool} {d t : ℕ} (h : IsDRTournamentWith Arc d t) {u v : ι}
include h

theorem BSLambda.IsDRTournamentWith.d_eq_two_mul_t_add_one [Nontrivial ι] : d = 2 * t + 1 := by sorry
