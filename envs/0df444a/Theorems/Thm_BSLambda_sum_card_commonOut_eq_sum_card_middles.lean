-- Prove2me | Theorems.Thm_BSLambda_sum_card_commonOut_eq_sum_card_middles
-- name    : BSLambda.sum_card_commonOut_eq_sum_card_middles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:10.061993+00:00
-- url     : https://prove2.me/theorems/84e17ff3-deee-41cd-89db-74f9d3a1e6d8
-- title:
--   BSLambda: sum card common Out eq sum card middles
-- statement:
--   Counting the arcs inside the out-neighbourhood of `u` by tail and by head: a pure
--   double-counting identity, with no regularity assumption on `Arc`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L145-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L145-L149

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
variable (Arc u)

theorem BSLambda.sum_card_commonOut_eq_sum_card_middles :
    ∑ y ∈ outNbrs Arc u, (commonOut Arc u y).card
      = ∑ y ∈ outNbrs Arc u, (middles Arc u y).card := by sorry
