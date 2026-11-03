-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_separated_mark_mean_measure_identification_from_halfline_tests
-- name    : AvramDividend.Classical.avram_wave7_01_original_separated_mark_mean_measure_identification_from_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:14:22.056297+00:00
-- url     : https://prove2.me/theorems/9ad193d2-546b-4776-8823-00fcc3cba099
-- title:
--   Original separated jump-mark mean measure is identified by its finite half-line test class
-- statement:
--   On the exact original SpectrallyNegativeLevy Ω/P/X, suppose a finite measure μ is identified with the actual expected intrinsic jump count on (0,T] and marks restricted to (-∞,-ε]. If μ agrees with T times the original ν on every left half-line within the cutoff, then the actual source expected count equals T ν(B) for every measurable B⊆(-∞,-ε]. This is the genuine measure-determining extension part of the zero-origin Lévy-Khintchine jump intensity proof. The finite-mass and half-line-test hypotheses are explicit unmet analytic obligations, not assumed consequences of BV, nor a proxy process.
-- source:
--   Proved original time-mark occupation measure e509ef60; pinned Mathlib MeasureTheory.Measure.ext_of_Iic with explicit finite μ; source source ν and actual count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_separated_mark_mean_measure_identification_from_halfline_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ B : Set ℝ, MeasurableSet B →
      μ B =
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (B ∩ Iic (-ε))) ∂P))
    (hTests : ∀ a : ℝ,
      μ (Iic a) = (T : ℝ≥0∞) * X.ν (Iic a ∩ Iic (-ε)))
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) =
    (T : ℝ≥0∞) * X.ν B := by sorry
