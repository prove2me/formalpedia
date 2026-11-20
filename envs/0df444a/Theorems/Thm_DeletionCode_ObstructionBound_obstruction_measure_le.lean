-- Prove2me | Theorems.Thm_DeletionCode_ObstructionBound_obstruction_measure_le
-- name    : DeletionCode.ObstructionBound.obstruction_measure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:02:13.340156+00:00
-- url     : https://prove2.me/theorems/2d3d7cec-d04e-49f6-86e5-d49e038e0951
-- title:
--   Obstruction Bound: obstruction measure le
-- statement:
--   The complete 1/12 obstruction bound, for explicit parameter inequalities.
--   The actual logarithmic choice supplies hbonus, and the size threshold depends only on t.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L70-L89
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionBound.lean#L70-L89

import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_ObstructionBound
set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionBound
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount
open CircleUniform WitnessCounting ObstructionProbability
open scoped BigOperators ENNReal

theorem DeletionCode.ObstructionBound.obstruction_measure_le {n : ℕ} (t k Q : ℕ) (ht : 2 ≤ t) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : 1 ≤ n)
    (hL : 4 * t + 2 ≤ windowLength k)
    (hbonus : ∀ R, windowLength k < R → n ≤ 2 ^ R)
    (hQ : 8 * scale t n k ≤ Q) (hQtwo : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (obstructionEvent t k Q x) ≤
      ENNReal.ofReal (1 / 12 : ℝ) := by sorry
