-- Prove2me | Theorems.Thm_BSLambda_IsDRTournamentWith_d_pos
-- name    : BSLambda.IsDRTournamentWith.d_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:22.062251+00:00
-- url     : https://prove2.me/theorems/5f3eacd0-d3e2-4d8e-a748-15dd461d129e
-- title:
--   Is DRTournament With: d pos
-- statement:
--   A doubly regular tournament with at least two vertices has positive out-degree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L224-L228
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L224-L228

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

theorem BSLambda.IsDRTournamentWith.d_pos [Nontrivial ι] : 0 < d := by sorry
