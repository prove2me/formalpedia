-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_aligned_dyadic_strict_sublevel_exhaustion
-- name    : AvramDividend.Classical.avram_ws01e_b_support_aligned_dyadic_strict_sublevel_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:36:50.368214+00:00
-- url     : https://prove2.me/theorems/f5418e95-a00d-49a5-97d3-54cb19fa2a93
-- title:
--   Strict path sublevel exhaustion by finite dyadic grids aligned with the horizon
-- statement:
--   For a right-continuous real path on nonnegative time, any positive finite horizon T and threshold a, there is a time t in [0,T] with f(t)<a if and only if a sampled value on one of the finite equal-mesh dyadic grids {kT/2^n : 0≤k≤2^n} is below a. The forward implication uses upward dyadic rounding of t/T, convergence from above, and right continuity; the reverse implication is a finite-grid inclusion. All grids contain both endpoints. This supplies the exact strict-event exhaustion needed to turn finite-mesh Lévy drawdown/minimum reversal into continuous-time threshold probability laws without assuming atomlessness at a.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid

open AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_support_aligned_dyadic_strict_sublevel_exhaustion (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    (∃ t : ℝ≥0, t ≤ T ∧ f t < a) ↔
      ∃ n : ℕ, ∃ k : ℕ, k ≤ 2 ^ n ∧
        f (((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) < a := by sorry
