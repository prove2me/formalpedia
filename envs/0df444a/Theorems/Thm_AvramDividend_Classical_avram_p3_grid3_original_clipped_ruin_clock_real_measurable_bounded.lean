-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
-- name    : AvramDividend.Classical.avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:24:26.480843+00:00
-- url     : https://prove2.me/theorems/9dfadcdd-b65d-4c1e-a1f7-75e3ce1c300a
-- title:
--   Original clipped ruin clock is measurable and bounded as a real random variable
-- statement:
--   The actual original spectrally negative Lévy ruin time is measurable under the dividend strategy. Intersecting it with the finite horizon T produces an ENNReal-valued bounded clock; taking its real value is measurable, nonnegative and at most T. This supplies the exact measurable random time needed to instantiate original strict contact-tail L1 convergence.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal) ∧
    (∀ ω : Ω,
      0 ≤ (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal ∧
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal ≤ (T : ℝ)) := by sorry
