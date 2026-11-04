-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uniform_real_grid_mean
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_uniform_real_grid_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:55:30.083936+00:00
-- url     : https://prove2.me/theorems/5837bbb5-d8b0-43ed-a5d6-86c123a5e851
-- title:
--   Original uniform Levy grid real Bochner expectation exactly equals cell-count times one-time expectation
-- statement:
--   For the actual spectrally negative Levy process and an arbitrary measurable real test integrable under the true original one-cell marginal, each term of the n+1-cell uniform grid is integrable and has identical genuine Bochner expectation. The exact full sum expectation is (n+1) times the one-time original marginal expectation. This is the missing original-source bridge from uniform L2/Vitali mesh convergence to the small-time Levy measure test rate, without assuming the rate conclusion or any substitute process law.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_width
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_stationary_real_integral

open MeasureTheory AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_uniform_real_grid_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hInt : Integrable
      (fun ω => g (X.X (T / ((n : ℝ≥0) + 1)) ω)) P) :
    (∫ ω, ∑ i ∈ Finset.range (n + 1),
      g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
         X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
    ((n : ℝ) + 1) *
      (∫ ω, g (X.X (T / ((n : ℝ≥0) + 1)) ω) ∂P) := by sorry
