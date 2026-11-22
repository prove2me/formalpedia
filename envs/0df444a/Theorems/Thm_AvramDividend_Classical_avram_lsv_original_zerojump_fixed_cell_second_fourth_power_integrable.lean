-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_fixed_cell_second_fourth_power_integrable
-- name    : AvramDividend.Classical.avram_lsv_original_zerojump_fixed_cell_second_fourth_power_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:17:05.824606+00:00
-- url     : https://prove2.me/theorems/9031e107-657a-4aab-a051-b125aaf9c157
-- title:
--   Original zero-jump physical centred Gaussian fixed-cell second and fourth powers are integrable
-- statement:
--   For the original Levy process with zero Levy measure and positive Gaussian coefficient, the true centred physical increment over an arbitrary deterministic time cell has finite second and fourth moments. Derive from the Proved quadratic-residual square integrability using elementary fourth-power dominance. This discharges the moment condition for products of right-continuously adapted original dividend atoms with Gaussian increments and squared increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gb52_original_positive_sigma_quadratic_cell_L2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_lsv_original_zerojump_fixed_cell_second_fourth_power_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s Δ : ℝ≥0) :
    let Z : Ω → ℝ := fun ω =>
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    Integrable (fun ω => (Z ω)^2) P ∧
      Integrable (fun ω => (Z ω)^4) P := by sorry
