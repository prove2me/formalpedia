-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:09:59.121433+00:00
-- url     : https://prove2.me/theorems/ff7fce2a-9dc0-4c42-85c2-6e6f8d7a5037
-- title:
--   Finite original jump selector indices are eventually injective from right endpoint convergence
-- statement:
--   Compose the already accepted separation of two selected uniform-grid indices with the already accepted finite simultaneous-injectivity theorem. If each selected right endpoint converges to its distinct true jump time, all cell selectors on a finite original jump set are jointly injective eventually. This supplies the injectivity premise needed for the complete original-grid compact-test limit.

import Mathlib
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
    (F : Finset ℝ≥0) (idx : ℝ≥0 → ℕ → ℕ) (w : ℕ → ℝ≥0)
    (hright : ∀ t ∈ F,
      Tendsto (fun n : ℕ => (((idx t n + 1 : ℕ) : ℝ≥0) * w n))
        atTop (𝓝 t)) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun t => idx t n) (F : Set ℝ≥0)  := by sorry
