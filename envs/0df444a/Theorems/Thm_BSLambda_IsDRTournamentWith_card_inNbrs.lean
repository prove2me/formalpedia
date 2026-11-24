-- Prove2me | Theorems.Thm_BSLambda_IsDRTournamentWith_card_inNbrs
-- name    : BSLambda.IsDRTournamentWith.card_inNbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:17.317429+00:00
-- url     : https://prove2.me/theorems/2c5c455e-2d85-4099-8a1f-4a216a970831
-- title:
--   Is DRTournament With: card in Nbrs
-- statement:
--   Every vertex of a doubly regular tournament has in-degree `d` as well.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L192-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L192-L200

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

theorem BSLambda.IsDRTournamentWith.card_inNbrs (i : ι) : (inNbrs Arc i).card = d := by sorry
