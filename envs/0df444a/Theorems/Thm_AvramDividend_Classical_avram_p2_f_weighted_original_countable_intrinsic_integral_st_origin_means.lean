-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_st_origin_means
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_integral_st_origin_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:51:24.2726+00:00
-- url     : https://prove2.me/theorems/40c31024-7e70-4713-a9bc-56153be4f1b7
-- title:
--   Original intrinsic countable predictable jump integral on arbitrary ordered (s,t] intervals
-- statement:
--   For countably many genuine original-process marked jump rectangles with individually varying ordered times s_i≤t_i, measurable negative or arbitrary Borel marks and adapted nonnegative weights, the expectation of the actual intrinsic marked jump measure integral equals the sum of the expected weights times the genuine original zero-origin expected counts of length t_i-s_i. No original ν-rate identity is assumed.
-- source:
--   Accepted original actual intrinsic countable integral theorem 144e9298-cc95-4450-9e69-245bc1b04188 and tsub_add_cancel_of_le endpoint identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_origin_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_integral_st_origin_means
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i)) :
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (t i - s i) ×ˢ B i) ∂P) := by sorry
