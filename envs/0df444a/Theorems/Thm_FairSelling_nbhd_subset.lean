-- Prove2me | Theorems.Thm_FairSelling_nbhd_subset
-- name    : FairSelling.nbhd_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:09.404917+00:00
-- url     : https://prove2.me/theorems/fce6d49e-1eab-49c2-baeb-f0035be5a011
-- title:
--   Fair Selling: nbhd subset
-- statement:
--   The Fair Selling construction uses the nbhd subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsMatching.lean#L50-L51
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsMatching.lean#L50-L51

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsMatching
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
omit [DecidableEq α] [DecidableEq β]

theorem FairSelling.nbhd_subset (B : Finset β) (acc : α → β → Prop) [DecidableRel acc] (a : α) :
    nbhd B acc a ⊆ B := by sorry
