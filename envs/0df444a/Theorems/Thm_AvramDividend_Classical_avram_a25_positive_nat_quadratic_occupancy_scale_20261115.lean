-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_positive_nat_quadratic_occupancy_scale_20261115
-- name    : AvramDividend.Classical.avram_a25_positive_nat_quadratic_occupancy_scale_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:15:14.374088+00:00
-- url     : https://prove2.me/theorems/876d8b98-cb28-4f8f-a01d-b55279d001c6
-- title:
--   Positive natural time-grid rescaling of a quadratic occupancy probability sandwich
-- statement:
--   Given a positive integer n and reals r,q, a quadratic bound r/n−(r/n)²/2≤q≤r/n rescales to r−r²/(2n)≤n q≤r. Prove by multiplying by the strictly positive n and clearing nonzero denominators. This is the purely algebraic step required to convert original physical marked-count first and second moment bounds at horizon T/n into the small-time void probability squeeze. It avoids mixing physical stochastic terms into field normalization.
-- source:
--   Nat positive cast, field_simp, ring, order-preserving multiplication.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_a25_positive_nat_quadratic_occupancy_scale_20261115
    (n : ℕ) (hn : 0 < n) (r q : ℝ)
    (h : r / (n : ℝ) - (r / (n : ℝ)) ^ 2 / 2 ≤ q ∧
      q ≤ r / (n : ℝ)) :
    r - (r ^ 2 / 2) * (1 / (n : ℝ)) ≤ (n : ℝ) * q ∧
      (n : ℝ) * q ≤ r := by sorry
