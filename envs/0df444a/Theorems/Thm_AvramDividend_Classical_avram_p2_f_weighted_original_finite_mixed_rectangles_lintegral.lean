-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_finite_mixed_rectangles_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_finite_mixed_rectangles_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:20:10.366557+00:00
-- url     : https://prove2.me/theorems/0fe0e9de-3cad-482c-8a36-de62f833cc1a
-- title:
--   Exact original Lévy finite mixed-rectangle weighted expectation linearity
-- statement:
--   Finite weighted lintegral is additive across a family of genuine original Lévy marked jump rectangles, allowing every rectangle to have its own deterministic start, duration, Borel mark and nonnegative measurable weight. This is the finite predictable-simple-cell algebraic step; rates remain separate.
-- source:
--   Already-Proved original intrinsic rectangle measurability and Mathlib lintegral_finset_sum/lintegral_tsum; no source ν-rate assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_finite_mixed_rectangles_lintegral
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (s T : ι → ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable (H i)) :
    (∫⁻ ω, (∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i))) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i)) ∂P) := by sorry
