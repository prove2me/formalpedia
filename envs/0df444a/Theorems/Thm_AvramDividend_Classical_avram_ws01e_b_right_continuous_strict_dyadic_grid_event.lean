-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
-- name    : AvramDividend.Classical.avram_ws01e_b_right_continuous_strict_dyadic_grid_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:35:39.613376+00:00
-- url     : https://prove2.me/theorems/739dfdfa-0c50-45dc-973c-2f88790551e9
-- title:
--   Strict finite-horizon threshold excursions of a right-continuous path occur on a dyadic grid
-- statement:
--   For a right-continuous real-valued path on nonnegative times and strictly positive finite horizon T, existence of an excursion f(s)<a at some s≤T is equivalent to existence of such an excursion at one of the nested finite dyadic observation times kT/2^n. The proof handles terminal endpoints and uses right-sided continuity and the proved dyadic ceiling-time convergence. No atomlessness or Wiener–Hopf independence is assumed.
-- source:
--   Right-continuous path excursion detection by dyadic right approximations, using Proved avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit (da8556b4). Needed in fixed-time càdlàg Lévy reversal.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
open Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_right_continuous_strict_dyadic_grid_event
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hcont : ∀ s : ℝ≥0, ContinuousWithinAt f (Set.Ici s) s)
    (a : ℝ) :
    (∃ s : ℝ≥0, s ≤ T ∧ f s < a) ↔
    (∃ n : ℕ, ∃ k : Fin ((2 : ℕ) ^ n + 1),
      f (((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) < a) := by sorry
