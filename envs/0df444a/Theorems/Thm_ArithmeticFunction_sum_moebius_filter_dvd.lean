-- Prove2me | Theorems.Thm_ArithmeticFunction_sum_moebius_filter_dvd
-- name    : ArithmeticFunction.sum_moebius_filter_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/7160e9c3-28be-5337-9944-ad6f68c1eeeb
-- title:
--   Möbius filter on divisors above a fixed divisor
-- statement:
--   Let $n$ and $m$ be natural numbers with $n \neq 0$ and $m \mid n$. The assertion is the identity, in $\mathbb{Z}$, $$\sum_{f \in \operatorname{divisors}(n)} \mu(n/f)\cdot\bigl[\,m \mid f\,\bigr] \;=\; \bigl[\,m = n\,\bigr],$$ where the sum is over the finite set of positive divisors $f$ of $n$, $\mu$ is the Möbius function of Mathlib's arithmetic-function library (valued in $\mathbb{Z}$), and each bracket denotes the value $1$ when the stated condition holds and $0$ otherwise: the summand is $\mu(n/f)$ multiplied by $1$ if $m$ divides $f$ and by $0$ otherwise, and the right-hand side is $1$ if $m$ equals $n$ and $0$ otherwise. Thus the divisor sum of $\mu(n/f)$ restricted to those divisors $f$ of $n$ that are divisible by $m$ collapses to the indicator of $f = n$ being the only such divisor, i.e. of $m = n$. The hypothesis $n \neq 0$ makes $\operatorname{divisors}(n)$ the usual set of divisors and the quotients $n/f$ meaningful; the hypothesis $m \mid n$ is used in the identification of the right-hand side.
--
--   This is the classical Möbius top-term filter: a divisor sum weighted by $\mu(n/f)$ and restricted to multiples of a fixed divisor $m$ retains only the term $f = n$. It serves as the elementary arithmetic input to the Möbius-inversion step in the treatment of Frobenius's density theorem, and is cited by [`FrobeniusDensity.sum_moebius_mul_pos`](thm.html#FrobeniusDensity.sum_moebius_mul_pos) and [`FrobeniusDensity.weight_eq`](thm.html#FrobeniusDensity.weight_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArithmeticFunction_sum_moebius_filter_dvd.lean

import Mathlib.NumberTheory.ArithmeticFunction.Moebius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ArithmeticFunction.Moebius

theorem ArithmeticFunction.sum_moebius_filter_dvd {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    ∑ f ∈ n.divisors, ArithmeticFunction.moebius (n / f) * (if m ∣ f then 1 else 0)
      = if m = n then 1 else 0 := by sorry
