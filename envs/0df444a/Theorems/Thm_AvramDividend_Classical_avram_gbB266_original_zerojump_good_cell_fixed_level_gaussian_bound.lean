-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB266_original_zerojump_good_cell_fixed_level_gaussian_bound
-- name    : AvramDividend.Classical.avram_gbB266_original_zerojump_good_cell_fixed_level_gaussian_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:54:54.284505+00:00
-- url     : https://prove2.me/theorems/7f1b4a16-f8bb-4061-817b-91f8654b1b96
-- title:
--   Original zero-jump unbounded-variation finite-dividend good-cell hit probability bound
-- statement:
--   For an original unbounded-variation zero-jump spectrally negative Levy source, every strictly positive physical-time increment has positive Gaussian variance. Hence for any adapted original monotone dividend strategy, the probability that the original reserve equals a prescribed fixed level at a time inside a cell with dividend increment at most epsilon is bounded by epsilon times the Gaussian density envelope at source variance. This specializes exact original-source Gaussian distribution, positivity of its variance, and the uniform random-centre small-ball good-cell estimate. It is a quantitative occupation input for the finite-cap fixed-level theorem B100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB266_original_zerojump_good_cell_fixed_level_gaussian_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t u : ℝ≥0) (hst : s < t) (htu : t < u)
    (x b epsilon : ℝ) (hEps : 0 ≤ epsilon) :
    P {ω | D u ω - D s ω ≤ epsilon ∧
      x + X.X t ω - rightLimit D t ω = b} ≤
      ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi *
          (((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * ((t - s : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
        ENNReal.ofReal epsilon := by sorry
