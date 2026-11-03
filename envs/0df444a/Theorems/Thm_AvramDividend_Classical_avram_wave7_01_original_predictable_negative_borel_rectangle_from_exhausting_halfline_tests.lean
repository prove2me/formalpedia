-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_predictable_negative_borel_rectangle_from_exhausting_halfline_tests
-- name    : AvramDividend.Classical.avram_wave7_01_original_predictable_negative_borel_rectangle_from_exhausting_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:58:33.124253+00:00
-- url     : https://prove2.me/theorems/ef819484-3e02-4dcb-ad40-910985aad053
-- title:
--   Original predictable Borel negative-mark rectangle from finite exhausting half-line tests
-- statement:
--   For the same original SpectrallyNegativeLevy on Ω and its actual filtration, a monotone measurable exhaustion of a negative Borel mark set by separated bands, together with explicit finite expected count and ν-intensity tests for each band cutoff, determines the unconditional jump-mark mean by finite-measure uniqueness and monotone convergence. Its genuine predictable past-event factorisation then yields the claimed all-negative rectangle compensator. No finite activity is inferred from BV.
-- source:
--   Proved original time-mark measure c026c74a, all-start halfline uniqueness 693d2adb, negative-band monotone extension 42393902 and past-event factorisation 264b3973.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave7_01_original_predictable_negative_borel_rectangle_from_exhausting_halfline_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (D : Set ℝ) (hD : MeasurableSet D)
    (C : ℕ → Set ℝ) (hCm : ∀ n, MeasurableSet (C n))
    (hCmono : Monotone C) (hCover : (⋃ n, C n) = D)
    (hTests : ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) ∧
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤ ∧
      ∀ a : ℝ,
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (Iic a ∩ Iic (-ε)))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ D) ∂P) =
    P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν D) := by sorry
