-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_tail_epsilon
-- name    : AvramDividend.Classical.avram_p2_i_moment_polynomial_tail_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:22:57.534204+00:00
-- url     : https://prove2.me/theorems/c9a565fb-2dc9-4938-bdcd-07d2fa2f65d7
-- title:
--   Weierstrass polynomial evaluation has arbitrarily small high-moment tail
-- statement:
--   For every real polynomial and positive epsilon there is a degree K at least its natural degree such that |p(z)| ≤ epsilon z^K for all z ≥ 2. The degree K is selected after the polynomial, so the result applies to a Weierstrass approximant even when the approximating positive measures have support beyond 1. It follows from finite-sum coefficient domination and geometric growth.

import Mathlib
open Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_polynomial_tail_epsilon
    (p : Polynomial ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, p.natDegree ≤ K ∧ ∀ z : ℝ, 2 ≤ z →
      |p.eval z| ≤ ε * z ^ K := by sorry
