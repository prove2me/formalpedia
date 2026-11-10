-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess17_actual_stopped_zero_contact_count_condExp_zero
-- name    : AvramDividend.Classical.avram_bv_excess17_actual_stopped_zero_contact_count_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:18:45.042412+00:00
-- url     : https://prove2.me/theorems/2db528c4-18ab-49e6-a9e8-5f0d992af740
-- title:
--   Original bounded-variation ruin-stopped zero-reserve negative count has source-centred conditional expectation
-- statement:
--   For each physical grid cell, the original strict-left controlled reserve is measurable at its start and the genuine strict survival indicator is measurable by the ruin stopping theorem. Their joint zero-contact stopped indicator is a bounded right-continuous past coefficient. The actual negative Lévy jump count on the future cell, centred by its finite activity rate, therefore remains conditionally mean zero under this same original mask. This is the concrete zero-boundary compensated source needed by the BV top-cap finite-activity diagonal 233260f7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess17_original_zero_prestate_source_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess17_actual_stopped_zero_contact_count_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (v : ℝ) :
    let J : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)))
       (Ioc s t ×ˢ Iio (0 : ℝ))
    P[(fun ω => (if (s : ℝ≥0∞) < ruinTime X x D ω ∧
        Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s = 0
      then v else 0) *
      ((J ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by sorry
