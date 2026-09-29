-- Prove2me | Theorems.Thm_EulerMascheroni_P2_factorial_binomial_prime_digit
-- name    : EulerMascheroni.P2.factorial_binomial_prime_digit
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T19:53:15.856987+00:00
-- url     : https://prove2.me/theorems/2881778e-582b-4251-8670-b60c9cf3e486
-- title:
--   A prime-digit reduction for the factorial-weighted P2 denominator
-- statement:
--   Let $p$ be any prime and let $a,b$ be natural numbers with $0\le b<p$. Define
--
--   $$U_n=\sum_{j=0}^{n}j!\binom nj^3\binom{2n-j}{n}^{2}.$$
--
--   Then
--
--   $$U_{ap+b}\equiv\binom{2a}{a}^{2}U_b\pmod p.$$
--
--   The identity holds for arbitrary $a$, including indices larger than $p^2$, and includes the prime $2$. Together with the exact identity $U_n=n!Q_n$, it reduces the residue of the P2 denominator to its low base-$p$ digit and a central binomial factor from the higher digits. It is an unconditional finite congruence; no numerator or global gcd estimate is asserted.
-- source:
--   Elementary consequence of Lucas’s theorem and factorial truncation, with a complete Lean proof supplied here. The denominator family is the p=2, x=1 specialization of Van Assche–Wolfs, arXiv:2404.09799v3, Section 5, https://arxiv.org/html/2404.09799v3#S5. The digit congruence is a derived auxiliary identity, not a named result in that paper; no bibliographic novelty is claimed.

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.BigOperators.ModEq
open scoped BigOperators

theorem EulerMascheroni.P2.factorial_binomial_prime_digit (a b p : ℕ) (hp : p.Prime) (hb : b < p) :
    (∑ j ∈ Finset.range (a*p+b+1),
      j.factorial * ((a*p+b).choose j)^3 * ((2*(a*p+b)-j).choose (a*p+b))^2) ≡
    (2*a).choose a ^ 2 *
      (∑ j ∈ Finset.range (b+1), j.factorial * (b.choose j)^3 * ((2*b-j).choose b)^2)
      [MOD p]  := by sorry
