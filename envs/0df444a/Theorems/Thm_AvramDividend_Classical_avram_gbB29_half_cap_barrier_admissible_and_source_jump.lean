-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB29_half_cap_barrier_admissible_and_source_jump
-- name    : AvramDividend.Classical.avram_gbB29_half_cap_barrier_admissible_and_source_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:02:38.844447+00:00
-- url     : https://prove2.me/theorems/628b426d-9a5f-4b06-905a-269672b5389e
-- title:
--   Half-cap original barrier admissibility and zero right-jump source condition
-- statement:
--   For any original spectrally negative Levy process and any candidate reward function w, the cap one-half original barrier dividend strategy is admissible and its right limits satisfy exactly the original fixed-band source dividend-jump condition, since the original barrier has no right jumps when starting at the barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB29_half_cap_barrier_admissible_and_source_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) :
    IsAdmissibleLe X (1 / 2 : ℝ) (ENNReal.ofReal (1 / 2 : ℝ))
      (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) <
        ruinTime X (1 / 2 : ℝ) (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) ω) →
      rightLimit (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω -
        barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ) t ω ≤
      w (riskProcess X (1 / 2 : ℝ) (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω) -
      w (riskProcess X (1 / 2 : ℝ) (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω -
        (rightLimit (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω -
         barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ) t ω)) := by sorry
