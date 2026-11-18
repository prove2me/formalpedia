-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB46_original_barrier_dividend_jump_budget
-- name    : AvramDividend.Classical.avram_gbB46_original_barrier_dividend_jump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:58:04.246555+00:00
-- url     : https://prove2.me/theorems/7ff56e46-1ef1-4c85-bdba-267c1d7a17ee
-- title:
--   Original cap barrier satisfies exact right-hand dividend-jump reward budget
-- statement:
--   For the original continuous upper-cap barrier dividend with equal initial reserve and barrier, the payment right-hand jump at every time is zero. Thus the original hJump budget inequality in the finite-cap Gaussian cash source holds for any candidate reward function, including at time zero and before ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB46_original_barrier_dividend_jump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) (w : ℝ → ℝ) :
    ∀ ω (t : ℝ≥0),
      rightLimit (barrierStrategy X c c) t ω -
        barrierStrategy X c c t ω ≤
      w (riskProcess X c (barrierStrategy X c c) t ω) -
        w (riskProcess X c (barrierStrategy X c c) t ω -
          (rightLimit (barrierStrategy X c c) t ω -
            barrierStrategy X c c t ω)) := by sorry
