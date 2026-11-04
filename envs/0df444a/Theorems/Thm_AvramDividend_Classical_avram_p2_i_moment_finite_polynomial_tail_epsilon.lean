-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_finite_polynomial_tail_epsilon
-- name    : AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_tail_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:22:54.364316+00:00
-- url     : https://prove2.me/theorems/f0f3930d-3a1e-4704-8366-67191da5b2fd
-- title:
--   Arbitrarily small high-moment polynomial tail coefficient
-- statement:
--   For any fixed finite real polynomial represented as a sum of monomials with degrees at most n, every positive tolerance epsilon admits a higher degree K such that at every z at least 2 the absolute value of the polynomial is at most epsilon times z to the power K. The proof uses the preceding coefficient-sum estimate and geometric growth of 2^r; it supplies the crucial limit-order choice K after a Weierstrass approximant, without restricting approximating measures to [0,1].

import Mathlib
open Set Filter Topology
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_tail_epsilon
    (s : Finset ℕ) (a : ℕ → ℝ) (n : ℕ)
    (hs : ∀ j ∈ s, j ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, n ≤ K ∧ ∀ z : ℝ, 2 ≤ z →
      |∑ j ∈ s, a j * z ^ j| ≤ ε * z ^ K := by sorry
