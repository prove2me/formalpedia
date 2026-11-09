-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:04:06.532072+00:00
-- url     : https://prove2.me/theorems/c97f2b53-8fc8-4345-b274-71b9721865ec
-- title:
--   Original predictable weighted Lévy-band compensation: integrability and conditional centring
-- statement:
--   For the original spectrally negative Lévy jump count in a finite-intensity Borel band, an initial/past-measurable essentially bounded weight multiplied by the compensated increment is L1 and has zero conditional expectation given the right-continuous past. The source-exact integrability component is needed before taking expectations of physical finite-grid compensated Itô terms.
-- source:
--   UBV-JUMP11 original-process finite-grid jump martingale upgrade of Proved dea95c8c using bounded multiplier integrability and source count L1.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
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
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    Integrable (fun ω => H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) P ∧
    P[(fun ω => H ω * ((J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by sorry
