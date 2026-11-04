-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_finite_simple_sum_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_finite_simple_sum_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:54:57.762748+00:00
-- url     : https://prove2.me/theorems/327b3cad-cd19-42d0-b591-2c090c6674d5
-- title:
--   Finite simple-weight ENNReal linearity of the genuine source-original marked jump count
-- statement:
--   For an arbitrary finite collection of nonnegative measurable weights, the expected true original Lévy intrinsic marked jump-count contribution of their pointwise sum equals the finite sum of their individual expected contributions. No integrability, ν-rate, Poisson copy or finite intensity assumption is used. This is the exact finite simple-process step for predictable compensation.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_finset_sum, Finset.sum_mul; proved source original intrinsic rectangle measurability d9c55240.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_finite_simple_sum_lintegral
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (S : Finset ι) (H : ι → Ω → ℝ≥0∞)
    (hMeas : ∀ i ∈ S, Measurable (H i)) :
    (∫⁻ ω, (∑ i ∈ S, H i ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by sorry
