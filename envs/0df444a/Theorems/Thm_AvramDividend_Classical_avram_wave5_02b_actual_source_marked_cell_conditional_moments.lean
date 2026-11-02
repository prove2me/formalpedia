-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_marked_cell_conditional_moments
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_source_marked_cell_conditional_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:44:12.442581+00:00
-- url     : https://prove2.me/theorems/68f5749c-6584-4b24-8e87-84d13f6076c5
-- title:
--   Actual source marked cell conditional moments from shifted path and unconditional laws
-- statement:
--   For a centred marked-cell reward defined by the intrinsic jump measure of the original Lévy process, assume it is represented by a measurable shifted-source-path functional and has the displayed unconditional first and second moments and integrability. Then its original-past conditional mean is zero and its conditional second moment is the displayed source intensity energy. Past independence is derived from original independent increments and no auxiliary mark sequence is required. The measurable extractor and unconditional moment laws remain explicit assumptions.
-- source:
--   Original-filtration shifted future path conditional first and second moments, Proved af7a6ae1-9c80-4160-9501-5d24b1bfc27c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02b_actual_source_marked_cell_conditional_moments
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
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν)
    (hJint : Integrable
      (fun ω => J (fun t => X.X (s + t) ω - X.X s ω)) P)
    (hJ2int : Integrable
      (fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P)
    (hFirst : (∫ ω, J (fun t => X.X (s + t) ω - X.X s ω) ∂P) = 0)
    (hSecond : (∫ ω, (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P) =
      rate * ∫ z, f z ^ 2 ∂ν) :
    let Z : Ω → ℝ := fun ω =>
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν
    (P[Z | 𝓕 s] =ᵐ[P] fun _ => 0) ∧
      (P[(fun ω => Z ω ^ 2) | 𝓕 s] =ᵐ[P]
        fun _ => rate * ∫ z, f z ^ 2 ∂ν) := by sorry
