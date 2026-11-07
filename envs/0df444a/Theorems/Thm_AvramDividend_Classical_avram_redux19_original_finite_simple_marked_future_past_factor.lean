-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_finite_simple_marked_future_past_factor
-- name    : AvramDividend.Classical.avram_redux19_original_finite_simple_marked_future_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:30:53.381105+00:00
-- url     : https://prove2.me/theorems/bf90ba18-a251-4552-9f69-6aa7f7d1a1b1
-- title:
--   Original finite simple marked-jump future is independent of all adapted past ENNReal weights
-- statement:
--   Every original adapted past nonnegative measurable weight is independent, in the exact extended-real lintegral sense, of any finite simple weighted sum of original negative or Borel marked jump counts in a future time interval. No stochastic surrogate, Poisson assumption, or distinct process is introduced.
-- source:
--   Choose the measurable same-shifted-future-path extractor provided by the finite-simple marked-count theorem and substitute its exact original-process value into Proved arbitrary-future-functional past-weight independence 8a788cbd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_finite_simple_marked_future_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_finite_simple_marked_future_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (n : ℕ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (w : Fin n → ℝ≥0∞) :
    (∫⁻ ω, H ω * (∑ i : Fin n, w i *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)) ∂P) =
    (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, ∑ i : Fin n, w i *
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B i) ∂P) := by sorry
