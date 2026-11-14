-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB306_original_real_time_good_cell_gaussian_fibre_bound
-- name    : AvramDividend.Classical.avram_gbB306_original_real_time_good_cell_gaussian_fibre_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:58:47.810249+00:00
-- url     : https://prove2.me/theorems/39394fcb-57fe-4016-be46-82bc119ea905
-- title:
--   Original Gaussian good-dividend-cell level-hit probability is bounded at every interior physical real time
-- statement:
--   For the genuine original zero-jump Gaussian Levy source, adapted dividends and every strictly interior real physical time in a fourth-power mesh interval, the probability of a fixed-level reserve hit with a small original dividend-cell increment is bounded by the original Gaussian conditional density reciprocal-square-root factor times the cubic inverse mesh threshold. This is the exact B266 conditional source bound transported from nonnegative-real source time to real physical-time sections, a crucial missing ingredient of B299.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB306_original_real_time_good_cell_gaussian_fibre_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (m i : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : t ∈ Set.Ioo
      ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
      (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))))
    (x b : ℝ) :
    P {ω | D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω ≤
          1 / ((m : ℝ) ^ 3) ∧
      x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω = b} ≤
    ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi *
        (((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) *
          ((Real.toNNReal t -
            ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
      ENNReal.ofReal (1 / ((m : ℝ) ^ 3)) := by sorry
