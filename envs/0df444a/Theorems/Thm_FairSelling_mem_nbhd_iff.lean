-- Prove2me | Theorems.Thm_FairSelling_mem_nbhd_iff
-- name    : FairSelling.mem_nbhd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:20.078459+00:00
-- url     : https://prove2.me/theorems/765684b4-8483-47d0-9606-dea4d0545167
-- title:
--   Fair Selling: mem nbhd iff
-- statement:
--   The Fair Selling construction uses the mem nbhd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsMatching.lean#L54-L56
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsMatching.lean#L54-L56

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsMatching
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
omit [DecidableEq α] [DecidableEq β]

theorem FairSelling.mem_nbhd_iff {B : Finset β} {acc : α → β → Prop} [DecidableRel acc] {a : α} {b : β} :
    b ∈ nbhd B acc a ↔ b ∈ B ∧ acc a b := by sorry
