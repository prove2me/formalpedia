-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_positive_gaussian_original_HJB_source
-- name    : AvramDividend.Classical.avram_gbB30_positive_gaussian_original_HJB_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:34:24.9402+00:00
-- url     : https://prove2.me/theorems/7c60c676-3abe-4687-83d0-5c93335b92bd
-- title:
--   Concrete positive Gaussian source with original Standing and HJB
-- statement:
--   Exhibit a concrete original c=2 sigma=1 zero-jump Brownian Levy source with Standing, unbounded variation, and exact generator-superharmonic and dividend-contact gradient properties for w(y)=2y-4y² on (0,1/8). Prerequisites are the separately proved source-model Standing, exact generator and local derivative theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_positive_gaussian_witness_standing
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_gaussian_generator_quadjet
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_quadratic_piecewise_positive_jets
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_positive_gaussian_original_HJB_source :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      (∀ y : ℝ, 0 < y → y < (1 / 8 : ℝ) →
        Y.GeneratorIntegrable (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ∧
        Y.generator (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y -
          (1 / 100 : ℝ) * (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y ≤ 0 ∧
        1 ≤ deriv (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y) := by sorry
