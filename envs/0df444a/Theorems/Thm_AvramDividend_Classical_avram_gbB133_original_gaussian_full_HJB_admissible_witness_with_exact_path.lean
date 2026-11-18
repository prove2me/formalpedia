-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
-- name    : AvramDividend.Classical.avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:44:50.088472+00:00
-- url     : https://prove2.me/theorems/34edaa16-da2f-4afb-8b9d-26531623d1f6
-- title:
--   Original Gaussian full HJB and barrier admissibility witness retains exact Brownian-plus-drift path
-- statement:
--   Strengthen the Proved positive-drift Gaussian full HJB/admissibility witness by retaining the exact canonical path equality Y.X_t=brownian(t)-brownian(0)+2t. The same witness has Standing, unbounded variation, the original piecewise quadratic candidate HJB generator and derivative conditions on (0,1/8), and admissible original cap barrier dividend. This makes it possible to instantiate source-faithful stopped physical-grid Brownian tube certificates and ultimately a counterexample to the disputed fixed-band cash bound without an assumed model relation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_gaussian_generator_quadjet
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_first_derivative
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_second_derivative
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_source_quad_regularity
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_barrier_no_initial_atom_source

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path :
    ∃ (𝓕 : Filtration ℝ≥0 (inferInstance :
        MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      (0 ≤ (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) 0) ∧ ContinuousOn (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) (Ici 0) ∧
      (∀ y : ℝ, y < 0 → (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y = 0) ∧
      ContDiffOn ℝ 2 (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal (1 / 8 : ℝ)} ∧
      (∀ y : ℝ, 0 < y → y < (1 / 8 : ℝ) →
        Y.GeneratorIntegrable (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ∧
        Y.generator (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y - (1 / 100 : ℝ) * (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ≤ 0 ∧
        1 ≤ deriv (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y) ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) := by sorry
