-- Prove2me | Theorems.Thm_DeletionCode_ObstructionBound_candidate_count_le
-- name    : DeletionCode.ObstructionBound.candidate_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:04:00.939242+00:00
-- url     : https://prove2.me/theorems/b2233556-44bf-4289-9181-e820d65dd180
-- title:
--   Obstruction Bound: candidate count le
-- statement:
--   The Obstruction Bound construction uses the candidate count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L17-L30
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L17-L30

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_ObstructionBound
set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal

theorem DeletionCode.ObstructionBound.candidate_count_le (t : ℕ) (ht : 2 ≤ t) (x : Letters) (n k R : ℕ)
    (hR : 2 ≤ R) (hx : KUnique x n k) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R)
    (hL : 4 * t + 2 ≤ windowLength k) (hcut : R ≤ cutoff t k) :
    Nat.card {U : RuleSet k // Candidate t x n k R U} ≤ (scale t n k) ^ R := by sorry
