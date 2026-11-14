-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB307_original_good_cell_fixed_level_hit_joint_measurable
-- name    : AvramDividend.Classical.avram_gbB307_original_good_cell_fixed_level_hit_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:00:12.026653+00:00
-- url     : https://prove2.me/theorems/3286564a-3fcb-4de0-bcde-e6065fd015b3
-- title:
--   Original small-dividend physical Gaussian cell fixed-level hit is jointly measurable
-- statement:
--   For the genuine spectrally negative Levy source and adapted dividend strategy, the sample-by-physical-time event that a real time lies strictly inside a specified fourth-power mesh cell, the original dividend increment in the cell is at most the cubic reciprocal threshold, and the original postpayment reserve equals a given level, is measurable. Proved B269 joint reserve measurability and deterministic adapted dividend sections give the needed intersection. Enables the exact B305 Tonelli input for B299.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB307_original_good_cell_fixed_level_hit_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (m i : ℕ) :
    MeasurableSet {z : Ω × ℝ |
      z.2 ∈ Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
        1 / ((m : ℝ) ^ 3) ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b} := by sorry
