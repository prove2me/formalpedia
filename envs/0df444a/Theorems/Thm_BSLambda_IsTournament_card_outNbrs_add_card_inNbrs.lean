-- Prove2me | Theorems.Thm_BSLambda_IsTournament_card_outNbrs_add_card_inNbrs
-- name    : BSLambda.IsTournament.card_outNbrs_add_card_inNbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:31.579839+00:00
-- url     : https://prove2.me/theorems/1edc4e3d-51c7-460f-ba42-9fa1062b2332
-- title:
--   Is Tournament: card out Nbrs add card in Nbrs
-- statement:
--   Out-neighbours and in-neighbours of a vertex partition the remaining vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L165-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L165-L169

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
variable {Arc : ι → ι → Bool} {i j l u v : ι}
open BSLambda.IsTournament
variable (h : IsTournament Arc)
include h
omit [DecidableEq ι]

theorem BSLambda.IsTournament.card_outNbrs_add_card_inNbrs (v : ι) :
    (outNbrs Arc v).card + (inNbrs Arc v).card + 1 = Fintype.card ι := by sorry
