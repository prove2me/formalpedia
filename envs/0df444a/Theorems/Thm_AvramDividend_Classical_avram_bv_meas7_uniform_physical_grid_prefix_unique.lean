-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uniform_physical_grid_prefix_unique
-- name    : AvramDividend.Classical.avram_bv_meas7_uniform_physical_grid_prefix_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:32:35.314588+00:00
-- url     : https://prove2.me/theorems/b832785c-1250-4098-9942-db010c5d21fe
-- title:
--   Original strict-prefix uniform physical grids coincide on every active cell
-- statement:
--   Any two nonnegative-real arrays of original strict-prefix physical grid clocks that start at zero at each horizon index and have the exact same uniform cell increment T/(n+2) must coincide at every active grid clock i<=n+1, for all n. The result is a deterministic uniqueness adapter that identifies separate source and predictability witnesses obtained from the same original physical-grid existence theorem, preventing an unproved same-grid substitution.
-- source:
--   Elementary NNReal-to-real coercion and induction on each finite physical prefix using exact equal cell widths. Used to identify the witnesses of two separately Proved original-process reductions a08ce531 (centred actual compensated X.nu martingale) and the physical-grid predictable-mask adapter, ensuring source and predictable mask share literally the same clock array. This theorem claims no stochastic cash or error identity.

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_prefix_uniform_physical_grid

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_uniform_physical_grid_prefix_unique
    (T : ℝ) (u v : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0) (hv0 : ∀ n, v n 0 = 0)
    (huWidth : ∀ n i, i < n + 1 →
      (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2))
    (hvWidth : ∀ n i, i < n + 1 →
      (v n (i + 1) : ℝ) - (v n i : ℝ) = T / ((n : ℝ) + 2)) :
    ∀ n i, i ≤ n + 1 → u n i = v n i := by sorry
