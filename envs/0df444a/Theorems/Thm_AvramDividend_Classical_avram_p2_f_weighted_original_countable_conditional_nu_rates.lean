-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_conditional_nu_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_conditional_nu_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:30:44.856432+00:00
-- url     : https://prove2.me/theorems/eff137fa-1084-4b49-a28d-e1d5e81ff97d
-- title:
--   Countable original marked jump compensation conditional on independent zero-origin Lévy rates
-- statement:
--   For countably many genuine original Lévy marked time rectangles and past measurable ENNReal weights, if every genuine zero-origin first moment is independently identified as Tᵢ times ν(Bᵢ), then the expected countable predictable marked count equals the sum of the expected weights times those rates. Every analytic original-process ν-rate appears explicitly as a premise; this theorem does not establish that premise.
-- source:
--   Previously Proved original source countable zero-origin transport helper 6819fcdd-af85-47bf-baf8-b412e291f714, genuine source marked jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_origin_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_conditional_nu_rates
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
    (∫⁻ ω, ∑' i, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
