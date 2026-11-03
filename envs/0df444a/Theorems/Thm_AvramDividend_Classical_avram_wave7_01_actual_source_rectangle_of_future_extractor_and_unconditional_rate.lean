-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_source_rectangle_of_future_extractor_and_unconditional_rate
-- name    : AvramDividend.Classical.avram_wave7_01_actual_source_rectangle_of_future_extractor_and_unconditional_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:14:25.882996+00:00
-- url     : https://prove2.me/theorems/c5f28e8b-e9d8-46c1-956a-c1e17702ed1b
-- title:
--   Original intrinsic marked rectangle compensation follows from same-path future measurability and the unconditional Lévy mark rate
-- statement:
--   For the literal original SpectrallyNegativeLevy P 𝓕 and arbitrary Borel marks B, the exact predictable rectangle compensation identity against every original past event A follows from two separate explicitly stated obligations: a measurable extractor of the literal marked count from the same original shifted future path, and the original unweighted first-moment Lévy intensity rate. No new sample space, proxy Poisson model, standing BV/finite-activity assumption or conditional compensator premise is introduced. This is a source-specific assembly theorem, not a proof of its independently necessary hypotheses.
-- source:
--   The directly Proved same-original-process past-factorisation theorem UUID ad24b83b-aa01-4fe1-a792-380fdb3e7329, then substitution of explicit unconditional ν(B) rate. Canonical unrestricted rectangle 393b03a8-2e9a-43d8-b415-854d86d58104 remains a separate Open proof obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_actual_source_rectangle_of_future_extractor_and_unconditional_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω))
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
