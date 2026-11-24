-- Prove2me | Theorems.Thm_BSLambda_sum_card_outNbrs_eq_sum_card_inNbrs
-- name    : BSLambda.sum_card_outNbrs_eq_sum_card_inNbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:08.261189+00:00
-- url     : https://prove2.me/theorems/c91f4a16-0f90-41c8-9c85-b3b5aee7b1a3
-- title:
--   BSLambda: sum card out Nbrs eq sum card in Nbrs
-- statement:
--   Counting the arcs of `Arc` by tail and by head.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L110-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L110-L113

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
variable {Arc : ι → ι → Bool} {i j : ι}
variable (Arc)

theorem BSLambda.sum_card_outNbrs_eq_sum_card_inNbrs :
    ∑ x, (outNbrs Arc x).card = ∑ x, (inNbrs Arc x).card := by sorry
