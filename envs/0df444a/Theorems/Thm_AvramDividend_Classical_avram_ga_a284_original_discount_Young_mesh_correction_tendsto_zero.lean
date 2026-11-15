-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a284_original_discount_Young_mesh_correction_tendsto_zero
-- name    : AvramDividend.Classical.avram_ga_a284_original_discount_Young_mesh_correction_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:28:26.639802+00:00
-- url     : https://prove2.me/theorems/37f02850-e51d-4c9a-9b4f-38050d5e2e54
-- title:
--   True original Gaussian physical discount Young quadratic mesh-count correction vanishes for every positive energy budget
-- statement:
--   On the original Gaussian physical n/(m+1) grid, the deterministic Young correction from absorbing the first-order discount source q Delta L |R| into eta raw-square energy equals m(q Delta L)^2/(4eta). For every fixed positive eta it vanishes as the grid refines. This is the exact original physical-grid source input from proved a206 and finite masked Young lemma a283 to close the a264 small-cell Gaussian expected tolerance budget.
-- source:
--   a206 original physical discount width squared mesh expected rate, eta fixed positive

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a284_original_discount_Young_mesh_correction_tendsto_zero
    (n : ℕ) (q L η : ℝ) (hη : 0 < η) :
    Tendsto (fun m : ℕ =>
      (m : ℝ)*(q*((((n : ℝ≥0) / ((m : ℝ≥0)+1)) : ℝ≥0) : ℝ)*L)^2/(4*η))
      atTop (𝓝 (0 : ℝ)) := by sorry
