-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
-- name    : AvramDividend.Classical.avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:34:10.555399+00:00
-- url     : https://prove2.me/theorems/693d2adb-0108-4b6d-ba39-5717babe60e5
-- title:
--   All-start original separated mark mean measure determined by half-line tests
-- statement:
--   On the exact original X and P and any physical interval (s,t], an explicitly finite expected intrinsic negative-cutoff mark measure μ matching ((t-s):ENNReal)ν on the left-halfline test class agrees with that same source ν on every Borel mark set contained in the cutoff. The halfline rate and measure finiteness are transparent analytic hypotheses. No BV finite activity or replacement Poisson model is assumed.
-- source:
--   Proved original time-mark occupation measure e509ef60; pinned Mathlib MeasureTheory.Measure.ext_of_Iic with explicit finite μ; source source ν and actual count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ B : Set ℝ, MeasurableSet B →
      μ B =
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P))
    (hTests : ∀ a : ℝ,
      μ (Iic a) = (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (Iic a ∩ Iic (-ε)))
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
    (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν B := by sorry
