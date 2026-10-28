-- Prove2me | Theorems.Thm_AvramDividend_Classical_exists_nat_filtration_along_monotone_nonnegative_time_grid
-- name    : AvramDividend.Classical.exists_nat_filtration_along_monotone_nonnegative_time_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:19:08.298436+00:00
-- url     : https://prove2.me/theorems/1bd7cbe7-2a13-41b2-b489-ce8718289354
-- title:
--   Every monotone nonnegative real-time grid induces a genuine natural-number filtration
-- statement:
--   Given an arbitrary filtration indexed by nonnegative real times and a monotone sequence of sampling times g:ℕ→ℝ≥0, there exists an honest natural-number-indexed filtration whose σ-algebra at discrete index n is exactly F_{g(n)}. This is the bridge required to instantiate Mathlib's discrete-time martingale constructor and maximal inequality for the projectively consistent finite Esscher martingale on any chosen time grid.
-- source:
--   Construct the discrete Filtration directly using the pinned Mathlib Filtration.mk constructor on the family n↦F_{g(n)}. Filtration.monotonicity and monotonicity of g prove its monotone field, while `𝓕.le (g i)` proves every grid σ-algebra lies under the ambient measurable space. Definitional equality yields the evaluation equation.

import Mathlib.Probability.Process.Filtration
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exists_nat_filtration_along_monotone_nonnegative_time_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (g : ℕ → ℝ≥0) (hg : Monotone g) :
    ∃ 𝓖 : Filtration ℕ mΩ, ∀ n : ℕ, 𝓖 n = 𝓕 (g n) := by sorry
