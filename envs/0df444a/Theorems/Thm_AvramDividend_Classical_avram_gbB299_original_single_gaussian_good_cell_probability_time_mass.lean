-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB299_original_single_gaussian_good_cell_probability_time_mass
-- name    : AvramDividend.Classical.avram_gbB299_original_single_gaussian_good_cell_probability_time_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T23:22:06.072199+00:00
-- url     : https://prove2.me/theorems/a497b3a1-dc2c-4559-abb0-d0aa2c0982fa
-- title:
--   One original Gaussian good-dividend physical cell has probability-time hit mass at most the fifth reciprocal mesh order
-- statement:
--   For the exact original zero-jump unbounded-variation spectrally negative Levy process and genuine adapted nondecreasing dividends, the physical-time product mass of a fixed-level reserve hit in a specified fourth-power mesh cell, provided the original dividend increment on that cell is at most the reciprocal cubic threshold, is bounded by twice the Gaussian density normalisation divided by the fifth power of the refinement. B266 gives the conditional independent Gaussian small-ball probability at every interior time and B268/B280/B293 integrate its reciprocal square-root elapsed-time envelope. This is the decisive single-cell probability step whose finite sum proves B296 and B276b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB299_original_single_gaussian_good_cell_probability_time_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (m i : ℕ) (hm : 0 < m) :
    (P.prod volume)
      {z : Ω × ℝ |
        z.2 ∈ Set.Ioo
          ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
          1 / ((m : ℝ) ^ 3) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} ≤
      (Real.toNNReal (2 /
        (X.σ * Real.sqrt (2 * Real.pi) * ((m : ℝ) ^ 5))) : ℝ≥0∞) := by sorry
