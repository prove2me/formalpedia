-- Prove2me | Theorems.Thm_DeletionCode_ObstructionBound_geometric_tail_le
-- name    : DeletionCode.ObstructionBound.geometric_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:02:43.459021+00:00
-- url     : https://prove2.me/theorems/e8e72347-766a-49b9-ad8f-955ddf3ceadb
-- title:
--   Obstruction Bound: geometric tail le
-- statement:
--   The Obstruction Bound construction uses the geometric tail le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L59-L66
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L59-L66

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_ObstructionBound
set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal

theorem DeletionCode.ObstructionBound.geometric_tail_le (M : ℕ) :
    (∑ R ∈ Finset.Icc 2 M, (1 / 4 : ℝ) ^ R) ≤ 1 / 12 := by sorry
