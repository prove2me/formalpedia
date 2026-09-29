-- Prove2me | Theorems.Thm_EulerMascheroni_P2_primitive_normalization
-- name    : EulerMascheroni.P2.primitive_normalization
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T19:44:14.699691+00:00
-- url     : https://prove2.me/theorems/1c1e4ded-965f-4da8-bf77-425f543ea094
-- title:
--   Exact primitive normalization and classification of integer scalings
-- statement:
--   Fix $n\ge0$ with $Q_n>0$. Let $b_n/a_n=P_n/Q_n$ be reduced with $a_n>0$, and put $c_n=a_n/Q_n$. Then
--
--   $$c_n>0,\qquad a_n=c_nQ_n,\qquad b_n=c_nP_n.$$
--
--   Moreover, whenever $c\ne0$ is real and $p=cP_n$, $q=cQ_n$ are integers, there is a nonzero integer $m$ such that
--
--   $$p=mb_n,\qquad q=ma_n,\qquad c=mc_n.$$
--
--   This identifies every integer normalization of this rational approximation. In particular, changing the initially chosen common denominator cannot improve upon the primitive multiplier.
-- source:
--   Derived auxiliary results for the p=2, x=1 family in Van Assche–Wolfs, Rational approximation of Euler’s constant using multiple orthogonal polynomials, arXiv:2404.09799v3, Section 5, displayed binomial formula for F_(n;2)^(I|p), https://arxiv.org/html/2404.09799v3#S5. The reduced-fraction normalization and conditional subsequence criterion are elementary deductions supplied here, not named statements or arithmetic-saving claims in that paper.

import Definitions.Def_eulerMascheroni_p2PrimitiveNormalization
open Filter Topology
open EulerMascheroni.P2

theorem EulerMascheroni.P2.primitive_normalization (n : ℕ) (hQ : 0 < Q n) :
    0 < primitiveQ n ∧ 0 < primitiveScale n ∧
    (primitiveQ n : ℝ) = primitiveScale n * (Q n : ℝ) ∧
    (primitiveP n : ℝ) = primitiveScale n * (P n : ℝ) ∧
    (∀ (c : ℝ), c ≠ 0 → ∀ p q : ℤ,
      (p : ℝ) = c * (P n : ℝ) → (q : ℝ) = c * (Q n : ℝ) →
      ∃ m : ℤ, m ≠ 0 ∧ p = m * primitiveP n ∧
        q = m * (primitiveQ n : ℤ) ∧ c = (m : ℝ) * primitiveScale n) := by sorry
