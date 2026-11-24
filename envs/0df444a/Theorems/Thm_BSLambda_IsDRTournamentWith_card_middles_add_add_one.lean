-- Prove2me | Theorems.Thm_BSLambda_IsDRTournamentWith_card_middles_add_add_one
-- name    : BSLambda.IsDRTournamentWith.card_middles_add_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:28.621437+00:00
-- url     : https://prove2.me/theorems/11eb278e-b139-405c-b270-5ec3f0cbf89a
-- title:
--   Is DRTournament With: card middles add add one
-- statement:
--   Along an arc `u → v` the out-neighbours of `u` split into `v` itself, the middles of the
--   arc, and the `t` common out-neighbours of `u` and `v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L210-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L210-L221

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

theorem BSLambda.IsDRTournamentWith.card_middles_add_add_one (huv : Arc u v) : (middles Arc u v).card + t + 1 = d := by sorry
