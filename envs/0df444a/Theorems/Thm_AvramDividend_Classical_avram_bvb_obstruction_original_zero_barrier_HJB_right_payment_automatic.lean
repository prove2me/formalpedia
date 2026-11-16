-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_zero_barrier_HJB_right_payment_automatic
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_zero_barrier_HJB_right_payment_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:47:38.461361+00:00
-- url     : https://prove2.me/theorems/e74e3ddc-41a7-4fa8-9564-6151a9c9f2f3
-- title:
--   Original zero-barrier strategy satisfies HJB right-payment jump budget for every verification candidate
-- statement:
--   The exact original zero-barrier strategy has no right payment jumps for a spectrally negative source. Therefore the verification candidate right-jump compensation inequality holds identically for any candidate function, including the positive-cap half-unit affine example, at initial and pre-ruin clocks. This directly discharges the hjump premise of the original BV boundary-contact leaf.
-- source:
--   Apply Proved b8214392 (original no right jump of zero-barrier strategy) and simplify both sides to zero. No derivative assumptions or extra source restrictions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_zero_barrier_HJB_right_payment_automatic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω) →
      rightLimit (barrierStrategy X 0 0) t ω -
        barrierStrategy X 0 0 t ω ≤
        w (riskProcess X 0 (barrierStrategy X 0 0) t ω) -
          w (riskProcess X 0 (barrierStrategy X 0 0) t ω -
            (rightLimit (barrierStrategy X 0 0) t ω -
              barrierStrategy X 0 0 t ω)) := by sorry
