-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_positive_laplace_kernel_min_linear_bound
-- name    : AvramDividend.Classical.excursion_positive_laplace_kernel_min_linear_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:21:00.11512+00:00
-- url     : https://prove2.me/theorems/da743bb0-938b-4269-9e85-465069aca014
-- title:
--   Positive Laplace Bernstein kernel dominated by s times the Lévy truncated jump height
-- statement:
--   For s≥1 and nonnegative height t, the Bernstein kernel satisfies 0≤1−e^(−st)≤s·min(1,t). On t≤1 use the global exponential tangent inequality 1−e^(−z)≤z; on t≥1 use 1−e^(−z)≤1≤s. Integrating this against a positive descending ladder-height Lévy measure with ∫min(1,t)<∞ yields the linear upper bound F(s)≤C s needed for strict full support of its killed potential.
-- source:
--   Pinned Mathlib Real.add_one_le_exp and Real.exp_le_one_iff; ladder-height Bernstein representation.

import Mathlib

theorem AvramDividend.Classical.excursion_positive_laplace_kernel_min_linear_bound
    (s t : ℝ) (hs : 1 ≤ s) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-(s * t)) ∧
      1 - Real.exp (-(s * t)) ≤ s * min 1 t := by sorry
