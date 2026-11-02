-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_predictable_cell_conditional_moments
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_predictable_cell_conditional_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:51:14.370196+00:00
-- url     : https://prove2.me/theorems/7ea47a29-c8cb-4d94-9fa4-48b57bda13aa
-- title:
--   Original predictable coefficient and actual marked-cell conditional moments
-- statement:
--   A past-measurable coefficient multiplying a compensated marked cell reward from the actual intrinsic jump measure has conditional mean zero and conditional second moment equal to the squared coefficient times source mark energy. The source reward must have a measurable shifted-future path representation, the stated unconditional first and second moments, and the displayed integrability properties. Original past independence is derived and no independent copy or auxiliary sequence is assumed.
-- source:
--   Proved original-filtration future-path conditional moments af7a6ae1-9c80-4160-9501-5d24b1bfc27c and pinned Mathlib conditional-expectation pull-out theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02b_actual_predictable_cell_conditional_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (C : Set ℝ) (f : ℝ → ℝ) (ν : Measure ℝ) (rate : ℝ)
    (H Z : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hH2 : StronglyMeasurable[𝓕 s] (fun ω => H ω ^ 2))
    (hZsource : ∀ ω, Z ω =
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν)
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) = Z ω)
    (hZi : Integrable Z P) (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hHZi : Integrable (H * Z) P)
    (hH2Z2i : Integrable (fun ω => H ω ^ 2 * Z ω ^ 2) P)
    (hFirst : (∫ ω, Z ω ∂P) = 0)
    (hSecond : (∫ ω, Z ω ^ 2 ∂P) = rate * ∫ z, f z ^ 2 ∂ν) :
    (P[H * Z | 𝓕 s] =ᵐ[P] fun _ => 0) ∧
    (P[(fun ω => (H ω * Z ω) ^ 2) | 𝓕 s] =ᵐ[P]
      fun ω => H ω ^ 2 * (rate * ∫ z, f z ^ 2 ∂ν)) := by sorry
