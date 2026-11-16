-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_nat_pgf_quadratic_factorial_upper_20261115
-- name    : AvramDividend.Classical.avram_a25_nat_pgf_quadratic_factorial_upper_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:10:21.646192+00:00
-- url     : https://prove2.me/theorems/512439d3-7736-4151-9ea5-b1fe82ae6b74
-- title:
--   Second-order quadratic upper bound for the probability-generating power z^k on the unit interval
-- statement:
--   For z in [0,1] and k≥0, the power z^k is bounded above by the second-order falling-factorial Taylor polynomial 1−(1−z)k+(1−z)²k(k−1)/2. Together with the already-Proved Bernoulli lower bound z^k≥1−(1−z)k, this gives a pointwise order-two approximation of the count PGF by its first two factorial moments. The original physical Lévy Borel count has exact first and second factorial source moments, giving a quadratic one-cell PGF error for a Bernoulli-grid Poisson limit.
-- source:
--   Induction using pow_succ; U_k z = U_{k+1} -(1-z)^3 k(k-1)/2 and 0≤(1-z)^3 k(k-1) for natural k.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_a25_nat_pgf_quadratic_factorial_upper_20261115
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (k : ℕ) :
    z ^ k ≤ 1 - (1 - z) * (k : ℝ) +
      (1 - z) ^ 2 * (k : ℝ) * ((k : ℝ) - 1) / 2 := by sorry
