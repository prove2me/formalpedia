-- Prove2me | Theorems.Thm_Brocard_berndt_galway_criterion
-- name    : Brocard.berndt_galway_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T02:30:17.00064+00:00
-- url     : https://prove2.me/theorems/a9f616c7-a841-4340-968c-456052e81d71
-- title:
--   Berndt–Galway criterion: a quadratic non-residue mod $p > n$ rules out $n!+1 = m^2$
-- statement:
--   Let $p$ be a prime and let $n < p$ be a natural number. Put
--   $$Q = (n+1)(n+2)\cdots(p-1) = \frac{(p-1)!}{n!}.$$
--   If $Q(Q-1)$ is a quadratic non-residue modulo $p$, that is,
--   $$\left(\frac{Q(Q-1)}{p}\right) = -1,$$
--   then $n! + 1$ is not a perfect square: $n! + 1 \neq m^2$ for every natural number $m$.
--
--   This is the criterion behind the computer search of Berndt and Galway for Brocard's equation $n! + 1 = m^2$. Wilson's theorem gives $n!\,Q \equiv -1 \pmod p$, so $Q^2(n!+1) \equiv Q(Q-1) \pmod p$. The value of $Q$ modulo $p$ takes only $p - n$ multiplications when $p$ is a prime just above $n$. One then looks for such a prime for which the Legendre symbol above is $-1$.
--
--   **Formalization Note.** $Q$ is written as `(p - 1).descFactorial (p - 1 - n)`, and the Legendre symbol is Mathlib's `legendreSym p`, applied to the integer $Q(Q-1)$.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard–Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), 41–42 (the sieve criterion used in their search).

import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace Brocard

theorem berndt_galway_criterion (n p : ℕ) [Fact p.Prime] (hn : n < p)
    (h : legendreSym p (((p - 1).descFactorial (p - 1 - n) : ℤ) *
      (((p - 1).descFactorial (p - 1 - n) : ℤ) - 1)) = -1)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by sorry

end Brocard
