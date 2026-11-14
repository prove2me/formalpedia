-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB296_original_gaussian_good_cell_probability_time_mass_bound
-- name    : AvramDividend.Classical.avram_gbB296_original_gaussian_good_cell_probability_time_mass_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T23:19:12.839613+00:00
-- url     : https://prove2.me/theorems/c1866435-a755-4831-b0ff-c77fd96d0525
-- title:
--   Original Gaussian controlled reserve good-grid fixed-level hits have total probability-time mass of inverse-refinement order
-- statement:
--   For the genuine zero-jump unbounded-variation spectrally negative Levy source, its true adapted nondecreasing dividend strategy and a prescribed reserve level, integrate fixed-level hits occurring in any fourth-power mesh cell whose original dividend increment is no more than the cubic reciprocal threshold. The true probability-by-physical-time product measure of this union of good-cell hit events is bounded by the original source Gaussian density constant 2n divided by mesh refinement m. This is the substantial original Gaussian probabilistic integration obligation remaining after the Proved source Gaussian small-ball, translated kernel, finite-grid, measurability and Fubini lemmas. No Gaussian marginal for the controlled reserve is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB296_original_gaussian_good_cell_probability_time_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n m : ℕ) (hm : 0 < m) :
    (P.prod volume)
      {z : Ω × ℝ | ∃ i ∈ Finset.range (n * m ^ 4),
        z.2 ∈ Set.Ioo
          ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
          1 / ((m : ℝ) ^ 3) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} ≤
      (Real.toNNReal ((2 * (n : ℝ)) /
        (X.σ * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
        (m : ℝ≥0∞)⁻¹ := by sorry
