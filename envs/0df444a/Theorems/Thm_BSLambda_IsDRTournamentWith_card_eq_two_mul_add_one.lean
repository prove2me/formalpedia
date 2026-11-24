-- Prove2me | Theorems.Thm_BSLambda_IsDRTournamentWith_card_eq_two_mul_add_one
-- name    : BSLambda.IsDRTournamentWith.card_eq_two_mul_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:56:19.449438+00:00
-- url     : https://prove2.me/theorems/30914756-8967-4364-8955-4f87fd48e5a0
-- title:
--   Is DRTournament With: card eq two mul add one
-- statement:
--   A doubly regular tournament on a nonempty `ι` has `2 * d + 1` vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L203-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L203-L206

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

theorem BSLambda.IsDRTournamentWith.card_eq_two_mul_add_one [Nonempty ι] : Fintype.card ι = 2 * d + 1 := by sorry
