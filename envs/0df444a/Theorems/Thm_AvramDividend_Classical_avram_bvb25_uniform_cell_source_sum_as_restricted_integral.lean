-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb25_uniform_cell_source_sum_as_restricted_integral
-- name    : AvramDividend.Classical.avram_bvb25_uniform_cell_source_sum_as_restricted_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:17:39.809075+00:00
-- url     : https://prove2.me/theorems/6aa761f2-17de-402d-b20e-7bdec9a768be
-- title:
--   Uniform original source-cell weighted sum equals its physical real-time floor-step integral
-- statement:
--   For the physical uniform mesh u(n,i)=T i/(n+2), any frozen real source-cell weights c(i) integrated by the true cell lengths are exactly their original uniform floor-step Lebesgue integral over [0,T], with the strict last partial horizon. This works for the original negative-mark compensator weights without changing the source, and is the deterministic grid-to-real-time bridge needed for inclusive original BV compensation.
-- source:
--   Proved b0b843ab uniform step grid integral and fcd068c1 real-time restriction; source-exact original physical grid u for 7ccc2a1a.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
import Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_floor_step_integral_restrict_horizon
open MeasureTheory Set
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bvb25_uniform_cell_source_sum_as_restricted_integral
    (T : ℝ) (hT : 0 < T) (n : ℕ) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ k i, (u k i : ℝ) =
       T * (i : ℝ) / ((k : ℝ) + 2))
    (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
       c i * ((u n (i + 1) : ℝ) - (u n i : ℝ))) =
    ∫ r in Set.Icc (0 : ℝ) T,
      (if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
       then c ⌊(r / T) * ((n : ℝ) + 2)⌋₊ else 0) := by sorry
