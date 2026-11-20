-- Prove2me | Theorems.Thm_DeletionCode_ObstructionBound_geometric_tail_identity
-- name    : DeletionCode.ObstructionBound.geometric_tail_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:02:46.532+00:00
-- url     : https://prove2.me/theorems/be2096ae-f5dc-4cfd-a3f9-8027275bb542
-- title:
--   Obstruction Bound: geometric tail identity
-- statement:
--   The Obstruction Bound construction uses the geometric tail identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L50-L57
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L50-L57

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_ObstructionBound
set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal

theorem DeletionCode.ObstructionBound.geometric_tail_identity (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 / 4 : ℝ) ^ (i + 2)) = (1 - (1 / 4 : ℝ) ^ N) / 12 := by sorry
