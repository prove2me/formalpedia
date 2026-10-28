-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierFutureRunningSup_rational_approx_of_local_bounds
-- name    : AvramDividend.Classical.barrierFutureRunningSup_rational_approx_of_local_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:41:29.2129+00:00
-- url     : https://prove2.me/theorems/ca483a69-382b-4d29-ac7e-b28f8d543afe
-- title:
--   AvramDividend.Classical.barrierFutureRunningSup_rational_approx_of_local_bounds
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.barrierFutureRunningSup_rational_approx_of_local_bounds from oversized parent candidate fcf98695524a14362cf237ed3c29b7b2eaafbdd6d99f2ab37359f5ac0a5c4003.
-- source:
--   candidate-decomposition:8fc83520-78bb-4a8c-a394-12b04a096b66:fcf98695524a14362cf237ed3c29b7b2eaafbdd6d99f2ab37359f5ac0a5c4003

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
import Theorems.Thm_AvramDividend_Classical_riskProcess_post_firstUpcrossing_ruin_iff
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_expected_shifted_stoppedReward
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem barrierFutureRunningSup_rational_approx_of_local_bounds
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (hf0 : f 0 = 0)
    (hRight : ∀ s : ℝ≥0, s < t → ∀ c : ℝ, c < f s →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ≥0,
        s < r → (r : ℝ) - (s : ℝ) < ε → c < f r)
    (hLeft : 0 < t → ∀ c : ℝ, c < f t →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ≥0,
        r < t → (t : ℝ) - (r : ℝ) < ε → c < f r) :
    ∀ s : Icc (0 : ℝ≥0) t, ∀ c : ℝ, c < max 0 (f s) →
      ∃ r : ℚ≥0, (r : ℝ≥0) ≤ t ∧ c < max 0 (f r) := by sorry
end AvramDividend.Classical
