-- Prove2me | Theorems.Thm_DeletionCode_WitnessCounting_componentIndex_card_le
-- name    : DeletionCode.WitnessCounting.componentIndex_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:30:29.659702+00:00
-- url     : https://prove2.me/theorems/60ac064d-5e8c-4751-8270-598f2af4f32f
-- title:
--   Witness Counting: component Index card le
-- statement:
--   The Witness Counting construction uses the component Index card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L38-L41
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L38-L41

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_WitnessCounting
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCounting
open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators

theorem DeletionCode.WitnessCounting.componentIndex_card_le (t k R : ℕ) :
    Fintype.card (ComponentIndex t k R) ≤ 2 * t * R + 1 := by sorry
