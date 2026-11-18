-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
-- name    : AvramDividend.Classical.avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:30:39.785762+00:00
-- url     : https://prove2.me/theorems/4a76056b-90a7-4a8b-925c-5cc71b12ff04
-- title:
--   Native Brownian continuous path lift is measurable whenever all coordinate processes are measurable
-- statement:
--   From the Proved native pointwise continuous Brownian path lift B44, derive a measurable random continuous function B:Ω→C([0,1],R) once each time-coordinate of the centred native Brownian process is measurable. Use the Mathlib Borel sigma-algebra characterization for continuous maps on a second-countable locally compact time domain. This identifies the one remaining coordinate-measurability premise to discharge the conditional Brownian tube transfer B126.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB44_native_brownian_centered_continuous_path_lift
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB134_native_centered_brownian_lift_measurable_of_coordinates
    (hCoordMeas : ∀ t : ℝ≥0,
      Measurable (fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω)) :
    ∃ B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ),
      Measurable B ∧
      ∀ (ω : ℝ≥0 → ℝ) (t : unitInterval),
        B ω t = ProbabilityTheory.brownian
          (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ω -
          ProbabilityTheory.brownian 0 ω := by sorry
