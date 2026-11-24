-- Prove2me | Theorems.Thm_BSLambda_IsDRTournamentWith_card_middles
-- name    : BSLambda.IsDRTournamentWith.card_middles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:27.569161+00:00
-- url     : https://prove2.me/theorems/2bd76ac8-2266-4473-90a7-84bb91313ab8
-- title:
--   Is DRTournament With: card middles
-- statement:
--   In a doubly regular tournament with at least two vertices, every arc `u → v` has exactly
--   `t` middle vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L254-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L254-L257

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

theorem BSLambda.IsDRTournamentWith.card_middles [Nontrivial ι] (huv : Arc u v) : (middles Arc u v).card = t := by sorry
