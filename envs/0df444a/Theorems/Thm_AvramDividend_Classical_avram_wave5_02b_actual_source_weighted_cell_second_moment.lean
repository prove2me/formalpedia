-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_weighted_cell_second_moment
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_source_weighted_cell_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:43:58.081221+00:00
-- url     : https://prove2.me/theorems/fdb61851-0650-4ef9-89c1-c454831b15d9
-- title:
--   Actual source weighted marked-cell L² isometry from a future-path second moment
-- statement:
--   For the original Lévy source and its intrinsic jump measure, a square-integrable past-measurable coefficient multiplying a compensated marked-cell reward satisfies the exact weighted second-moment identity. Independence of the squared coefficient and squared reward is derived from the original shifted future-path independence. Existence of a measurable source-path extractor and its unconditional marked-cell second moment are explicitly assumed. No infinite auxiliary marks or change of sample space is introduced.
-- source:
--   Original future-path extractor independence 86ab54a5-0f9f-4e69-a76c-19f22db4d908 and pinned Mathlib independent-product integrability and expectation factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02b_actual_source_weighted_cell_second_moment
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
    (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν)
    (hJ2int : Integrable
      (fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P)
    (hSecond : (∫ ω, (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P) =
      rate * ∫ z, f z ^ 2 ∂ν) :
    let Z : Ω → ℝ := fun ω =>
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν
    Integrable (fun ω => (H ω * Z ω) ^ 2) P ∧
      (∫ ω, (H ω * Z ω) ^ 2 ∂P) =
        (∫ ω, H ω ^ 2 ∂P) * (rate * ∫ z, f z ^ 2 ∂ν) := by sorry
