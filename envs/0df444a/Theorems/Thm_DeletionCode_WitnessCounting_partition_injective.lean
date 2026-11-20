-- Prove2me | Theorems.Thm_DeletionCode_WitnessCounting_partition_injective
-- name    : DeletionCode.WitnessCounting.partition_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:30:28.562299+00:00
-- url     : https://prove2.me/theorems/46b1f813-f264-4d1f-916a-dbc3fa9cd04e
-- title:
--   Witness Counting: partition injective
-- statement:
--   The Witness Counting construction uses the partition injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L79-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L79-L84

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

theorem DeletionCode.WitnessCounting.partition_injective (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 1 ≤ R) :
    Function.Injective (partition t ht x n k R hR) := by sorry
