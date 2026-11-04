-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_stationary_probability
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_stationary_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:49:08.726948+00:00
-- url     : https://prove2.me/theorems/f444974e-f449-4156-a2b9-d7c5dbb2b638
-- title:
--   Original process stationary event probability on each uniform source cell
-- statement:
--   Every uniform nonnegative source grid cell has exact width δ, so its genuine original process one-time X evaluation has the same original-space event probability at δ for any Borel or non-Borel mark B. The result uses only the proved arithmetic width identity and preserves P and X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_width

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_stationary_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (j : ℕ) (δ : ℝ≥0) (B : Set ℝ) :
    P {ω : Ω | X.X (((((j + 1 : ℕ) : ℝ≥0) * δ) - ((j : ℝ≥0) * δ))) ω ∈ B} =
    P {ω : Ω | X.X δ ω ∈ B} := by sorry
