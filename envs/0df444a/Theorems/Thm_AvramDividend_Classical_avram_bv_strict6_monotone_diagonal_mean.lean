-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_monotone_diagonal_mean
-- name    : AvramDividend.Classical.avram_bv_strict6_monotone_diagonal_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:20:51.824258+00:00
-- url     : https://prove2.me/theorems/ce0501a7-25ae-41ee-b4d5-0f2b102cd3ff
-- title:
--   Strictly increasing diagonal of nonnegative physical mesh errors
-- statement:
--   If each fixed compact-band expected physical source error is nonnegative and vanishes as the original-process mesh refines, one can select strictly increasing mesh levels phi(k) at least k with the diagonal errors tending to zero. This is conditional on genuine source convergence and yields a cofinal selector suitable for strict-horizon clock arguments.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_nonnegative_error_mean
open Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_monotone_diagonal_mean
    (E : ℕ → ℕ → ℝ)
    (hnonneg : ∀ k n, 0 ≤ E k n)
    (hvanish : ∀ k, Tendsto (fun n => E k n) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ k, k ≤ φ k) ∧
      Tendsto (fun k => E k (φ k)) atTop (𝓝 0) := by sorry
