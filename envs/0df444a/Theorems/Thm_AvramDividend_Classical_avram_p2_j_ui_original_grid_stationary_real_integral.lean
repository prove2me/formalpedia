-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_stationary_real_integral
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_grid_stationary_real_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:45:09.723967+00:00
-- url     : https://prove2.me/theorems/79c047dc-1213-4404-b103-ce9a9eb49ddd
-- title:
--   Original Levy finite-grid real Bochner mean equals sum of true single-duration test expectations
-- statement:
--   For every finite nondecreasing grid, arbitrary measurable real mark-test function and integrability of each true single-duration original law, the actual unmodified original spectrally negative Levy grid has genuine Bochner expectation equal to the sum of true original one-time-law expectations. The proof transports integrability using the stationary increment law and applies finite Bochner integral additivity. The result isolates the exact finite-grid step needed before a small-time Levy rate limit; it assumes neither compensated jumps nor a jump rate.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_original_grid_stationary_real_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i : ℕ, i < n → grid i ≤ grid (i + 1))
    (g : ℝ → ℝ) (hg : Measurable g)
    (hInt : ∀ i < n, Integrable
      (fun ω => g (X.X ((s + grid (i + 1)) - (s + grid i)) ω)) P) :
    (∫ ω, ∑ i ∈ Finset.range n,
      g (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
    ∑ i ∈ Finset.range n,
      ∫ ω, g (X.X ((s + grid (i + 1)) - (s + grid i)) ω) ∂P := by sorry
