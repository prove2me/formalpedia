-- Prove2me | Theorems.Thm_DeletionCode_ObstructionBound_survival_term_le
-- name    : DeletionCode.ObstructionBound.survival_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:02:27.605093+00:00
-- url     : https://prove2.me/theorems/03f5b4c3-96c0-4da4-93bb-999f0369ae8a
-- title:
--   Obstruction Bound: survival term le
-- statement:
--   The Obstruction Bound construction uses the survival term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L32-L48
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L32-L48

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_ObstructionBound
set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal

theorem DeletionCode.ObstructionBound.survival_term_le (C N Q R : ℕ) (hC : C ≤ N ^ R) (hQ : 8 * N ≤ Q)
    (hQpos : 0 < Q) :
    (C : ENNReal) * ENNReal.ofReal (2 / (Q : ℝ)) ^ R ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ R) := by sorry
