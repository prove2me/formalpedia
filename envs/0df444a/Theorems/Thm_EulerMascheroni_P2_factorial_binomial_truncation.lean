-- Prove2me | Theorems.Thm_EulerMascheroni_P2_factorial_binomial_truncation
-- name    : EulerMascheroni.P2.factorial_binomial_truncation
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T19:03:42.589976+00:00
-- url     : https://prove2.me/theorems/10fe549f-f3f2-4e11-b0bf-807808e6b79b
-- title:
--   Fixed-modulus truncation of the factorial-binomial Euler coefficient
-- statement:
--   Put
--   $$U_n=\sum_{j=0}^n j!\binom nj^3\binom{2n-j}{n}^2.$$
--   For any natural modulus $q$ and cutoff $J$ such that $q\mid J!$, one has
--   $$U_n\equiv\sum_{0\le j<\min(n+1,J)}j!\binom nj^3\binom{2n-j}{n}^2\pmod q.$$
--   Every omitted term is divisible by $J!$. Reindexing $j=n-k$ identifies $U_n$ with
--   $$n!\sum_{k=0}^n\binom nk^2\binom{n+k}k^2\frac1{k!},$$
--   the integer coefficient attached to the order-two family in Van Assche–Wolfs, Section 5. The reindexing identity is explanatory context; the formal statement is the displayed congruence.
--
--   For a fixed prime power $q=p^r$, the cutoff depends only on $p,r$, not on $n$. This permits an explicit finite rational-diagonal representation modulo $p^r$ and connects the coefficient sequence to automatic congruence methods. Those additional representation and automaticity arguments are not asserted as Lean dependencies or conclusions of this theorem. This elementary lemma does not prove any irrationality assertion.
-- source:
--   Elementary factorial divisibility, derived for the integer coefficient of the order-two family in Van Assche–Wolfs, Rational approximation of Euler’s constant using multiple orthogonal polynomials, Section 5, https://arxiv.org/html/2404.09799v3. Motivation: Rowland–Yassawi, Automatic congruences for diagonals of rational functions, Theorem 2.1, https://www.numdam.org/item/10.5802/jtnb.901.pdf. The congruence is derived here, not quoted as a theorem of either paper; no bibliographic novelty is claimed.

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open scoped BigOperators

theorem EulerMascheroni.P2.factorial_binomial_truncation (n q J : ℕ) (h : q ∣ J.factorial) :
    (∑ j ∈ Finset.range (n+1),
      j.factorial * (n.choose j)^3 * ((2*n-j).choose n)^2) ≡
    (∑ j ∈ Finset.range (min (n+1) J),
      j.factorial * (n.choose j)^3 * ((2*n-j).choose n)^2) [MOD q] := by sorry
