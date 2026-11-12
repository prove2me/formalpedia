-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_frozen_grid_sum_as_step_integral
-- name    : AvramDividend.Classical.avram_bvb_b21_original_frozen_grid_sum_as_step_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:45:16.703143+00:00
-- url     : https://prove2.me/theorems/33698ce5-555d-42bc-ba21-5cb855970d7e
-- title:
--   Exact integral representation of the original frozen uniform-grid loss sum
-- statement:
--   Every finite frozen marked-loss grid sum with monotone time nodes equals the Lebesgue integral of its actual piecewise-constant half-open-cell sampled kernel, retaining the exact cell widths.
-- source:
--   Root-connected analytic bridge for original finite-cap phys95 and later-ruin quadrature: substitutes the genuine uniform-grid J sum by a measure integral before one-sided reverse Fatou.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_frozen_grid_sum_as_step_integral
    (N : ℕ) (u c : ℕ → ℝ)
    (hu : ∀ i < N, u i ≤ u (i + 1)) :
    (∫ t : ℝ, ∑ i ∈ Finset.range N,
      (Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) =
      ∑ i ∈ Finset.range N, (u (i + 1) - u i) * c i := by sorry
