-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB31_concrete_gaussian_source_package
-- name    : AvramDividend.Classical.avram_gbB31_concrete_gaussian_source_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:48:33.830579+00:00
-- url     : https://prove2.me/theorems/dd4aa79c-9055-453c-98dc-cdcc3141812a
-- title:
--   Fully source-admissible positive drift Gaussian stopped-dividend candidate
-- statement:
--   Exhibit the original Gaussian Levy process with c=2,sigma=1,no jumps, Standing and unbounded variation, the piecewise quadratic candidate reward meeting the exact C2 and generator sign hypotheses on cap 1/8, and the original barrier dividend strategy satisfying admissibility. This is the complete static source witness package for fixed-band Gaussian analysis; the stopped physical-grid cash and positive probability event remain separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_positive_gaussian_witness_standing
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB31_concrete_gaussian_source_package :
    ∃ (𝓕 : Filtration ℝ≥0 (inferInstance :
        MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
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
