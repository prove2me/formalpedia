-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:44:18.115501+00:00
-- url     : https://prove2.me/theorems/f9f62551-ec9a-448d-b5ac-4e65ab1f90ef
-- title:
--   True source countable intrinsic jump-measure integral conditional on original Lévy rates
-- statement:
--   An actual original Lévy-process countable family of predictably selected jump rectangles satisfies the expected weighted integral equality with the corresponding Lévy measure rates, conditional on the exact original zero-origin count rate as an explicit hypothesis for each Borel mark. No zero-origin ν identity is smuggled into the proof.
-- source:
--   Proved actual original source zero-origin helper AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_integral_origin_means with independent original-process rate assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_origin_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates
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
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) = (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
