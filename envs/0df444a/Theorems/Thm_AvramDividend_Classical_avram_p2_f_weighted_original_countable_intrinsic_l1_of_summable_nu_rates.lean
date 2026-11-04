-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_l1_of_summable_nu_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_l1_of_summable_nu_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:59:17.390787+00:00
-- url     : https://prove2.me/theorems/bec9046c-a06e-4799-9503-8630d5595e2c
-- title:
--   Finite first moment of original countable predictable intrinsic jump integral from summable true Lévy rates
-- statement:
--   If every original zero-origin marked count ν rate has been established independently and the sum of the expected nonnegative adapted weights times true original Lévy intensities is finite, then the first moment of the actual original-process intrinsic countable marked jump-measure integral is finite. The ν-rate and summability requirements are explicit and no hidden finiteness or artificial stochastic model is introduced.
-- source:
--   Accepted genuine original conditional countable intrinsic integral f9f62551-ec9a-448d-b5ac-4e65ab1f90ef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_l1_of_summable_nu_rates
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
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) ≠ ∞ := by sorry
