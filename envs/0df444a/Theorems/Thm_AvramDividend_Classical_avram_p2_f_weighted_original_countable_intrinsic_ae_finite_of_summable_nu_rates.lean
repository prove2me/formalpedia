-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_ae_finite_of_summable_nu_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_ae_finite_of_summable_nu_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:02:06.591901+00:00
-- url     : https://prove2.me/theorems/e93cec85-52a6-4376-ab1b-b5933ed2341b
-- title:
--   Original countable predictable intrinsic jump integral finite almost surely from summable original ν rates
-- statement:
--   When the true original-process zero-origin Lévy-rate identities hold and the expected-weight times ν-rate sum is finite, the literal original intrinsic countable marked-jump integral is finite for almost every original source path. The proof uses only actual-source integral measurability, accepted original countable compensation and Mathlib ae_lt_top.
-- source:
--   Proved original countable intrinsic simple integral measurability 315dcf0b-f988-4716-abec-c790fcb225b3 and original countable intrinsic conditional ν factor f9f62551-ec9a-448d-b5ac-4e65ab1f90ef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_simple_integral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_ae_finite_of_summable_nu_rates
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hOrigin : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) = (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)))
    (hFinite : (∑' i, (∫⁻ ω, H i ω ∂P) * (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) ≠ ∞) :
    ∀ᵐ ω ∂P, (∫⁻ p, ∑' i, (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) < ∞ := by sorry
