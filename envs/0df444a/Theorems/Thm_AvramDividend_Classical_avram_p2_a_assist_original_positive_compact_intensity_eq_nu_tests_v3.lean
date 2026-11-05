-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_positive_compact_intensity_eq_nu_tests_v3
-- name    : AvramDividend.Classical.avram_p2_a_assist_original_positive_compact_intensity_eq_nu_tests_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:09:53.22354+00:00
-- url     : https://prove2.me/theorems/b29f8e04-4bf5-4737-ac8a-cce0918f64e3
-- title:
--   Original intensity has genuine compact negative Lévy test expectations
-- statement:
--   Construct the source-exact all-horizon marked intensity and prove its nonnegative compact continuous negative-test moments equal the genuine original Lévy measure's moments for every such test, without an extra cutoff, by invoking the Proved intrinsic source J formula, exact counting-to-sum bridge and separated-support lemma.
-- source:
--   New public original time-one intensity Tonelli and source-specific finite count-to-jump conversion, combined with Proved public original J L1 formula a09f7014-b563-4d3a-9911-03825b524893.

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_finite_jump_test_count_integral_v2
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_support_separated

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_assist_original_positive_compact_intensity_eq_nu_tests_v3
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ σ : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ B) ∂P) =
          (T : ℝ≥0∞) * σ B) ∧
      (∀ (f : ℝ → ℝ) (hf : Continuous f)
          (hc : IsCompact (tsupport f))
          (hneg : tsupport f ⊆ Iio (0 : ℝ))
          (hfnonneg : ∀ y : ℝ, 0 ≤ f y),
        (∫⁻ y, ENNReal.ofReal (f y) ∂σ) =
          ENNReal.ofReal (∫ y, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) ∧
      (∀ ε : ℝ, 0 < ε → σ (Iic (-ε)) < ⊤) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        σ B = σ (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite σ := by sorry
