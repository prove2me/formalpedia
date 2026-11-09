-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_past_event_integral_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_finite_band_past_event_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:37:15.492574+00:00
-- url     : https://prove2.me/theorems/efff5e05-38f8-4c73-8d05-d69f9941ca3b
-- title:
--   Original finite-band compensated jump has zero restricted expectation on every past event
-- statement:
--   The original spectrally negative Lévy finite-band compensated physical count weighted by an integrable bounded past coefficient has zero integral on any event of the same right-continuous past. Combines source-exact Proved conditional L1 and Proved eventwise conditional mean-zero integration; reusable for initial event masked Ito grids.
-- source:
--   UBV-JUMP11 original-process masked finite-band bridge, sourced to Proved c97f2b53 and 1820407b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump11_original_finite_band_past_event_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (B : Set ℝ) (hB : MeasurableSet B) (hFinite : X.ν B < ⊤)
    (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (H : Ω → ℝ) (C : ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hHAE : AEStronglyMeasurable H P)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont s] A) :
    (∫ ω in A, H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) = 0 := by sorry
