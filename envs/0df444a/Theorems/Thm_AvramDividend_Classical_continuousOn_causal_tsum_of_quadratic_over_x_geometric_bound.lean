-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound
-- name    : AvramDividend.Classical.continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:21:36.165569+00:00
-- url     : https://prove2.me/theorems/e3188f4f-903f-40ca-a3c9-598ba4d1251f
-- title:
--   Continuous positive-time renewal series from quadratic-geometric over-x bound
-- statement:
--   If a family f_n is continuous on (0,∞) and ‖f_n(x)‖≤n²ρⁿ/x for 0<ρ<1, its pointwise sum is continuous on (0,∞). Although the estimates are singular at zero, every positive x has a neighbourhood bounded away from zero, on which the existing quadratic-geometric M-test applies.
-- source:
--   Composes the Proved uniform-above-cutoff bound with the Proved quadratic-geometric M-test and the newly Proved causal convolution-power continuity theorem; isolates local uniform convergence in the BV Esscher renewal-density argument 17bc0aad-807f-4e33-82d9-b8a65d2b6166.

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_continuousOn_tsum_of_quadratic_geometric_bound
open AvramDividend.Classical MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound
    (f : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hf : ∀ n : ℕ, ContinuousOn (f n) (Ioi (0 : ℝ)))
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      ‖f n x‖ ≤ ((n : ℝ) ^ 2 * ρ ^ n) / x) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, f n x) (Ioi (0 : ℝ)) := by sorry
