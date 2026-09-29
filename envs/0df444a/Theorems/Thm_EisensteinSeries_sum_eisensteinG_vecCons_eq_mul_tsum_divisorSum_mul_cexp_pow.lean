-- Prove2me | Theorems.Thm_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow
-- name    : EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/faa7043a-9f5d-5d08-a50f-6a3f813098e8
-- title:
--   q-expansion of level-N Eisenstein series summed over one row class
-- statement:
--   Let $N$ be a positive natural number, let $a \in \mathbb{Z}/N$ with $a \neq 0$, let $k$ be a natural number with $3 \le k$ and $k$ even, and let $z$ lie in the upper half-plane. For $v \in (\mathbb{Z}/N)^2$, [`EisensteinSeries.eisensteinG N k v z`](def/EisensteinSeries_EisensteinG.html#L5) is the sum of `eisSummand k w z`, i.e. of $(w_0 z + w_1)^{-k}$, over all $w \in \mathbb{Z}^2$ whose componentwise reduction modulo $N$ equals $v$ — the full congruence class, with no coprimality condition imposed. The assertion is that $$\sum_{e \in \mathbb{Z}/N} \mathrm{eisensteinG}\,N\,k\,(a,e)\,(z) = \frac{(-2\pi i)^k}{(k-1)!} \sum_{n \ge 0} \Big( \sum_{d \mid n} \big( [\,n/d \equiv a\,]\, d^{k-1} + [\,n/d \equiv -a\,]\, d^{k-1} \big) \Big) q^n,$$ where $q = \exp(2\pi i z)$, the bracket denotes the indicator of the stated congruence in $\mathbb{Z}/N$, and the inner sum runs over the divisors of $n$ (so the $n = 0$ term vanishes). The coefficient is written as a sum of two separate indicator terms, so for $n/d$ with $a = -a$ a divisor contributes twice.
--
--   This is the Lipschitz–Hecke $q$-expansion for Eisenstein series of level $N$, here in the form obtained by summing the series over all rows congruent to a fixed nonzero first residue $a$; the hypothesis $a \neq 0$ removes the row $m = 0$ and hence the constant term, and evenness of $k$ identifies the rows $m$ and $-m$. It supplies the explicit expansion used in [`ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq`](thm.html#ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq), where a weight-four form with integral $q$-expansion and prescribed partial divisor-sum coefficients is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow.lean

import Mathlib
import Definitions.Def_EisensteinSeries_EisensteinG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real in

theorem EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow
    (N : ℕ) [NeZero N] (a : ZMod N) (ha : a ≠ 0) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : UpperHalfPlane) :
    ∑ e : ZMod N, EisensteinSeries.eisensteinG N k ![a, e] z =
      ((-2 * π * Complex.I) ^ k / (Nat.factorial (k - 1) : ℂ)) *
        ∑' n : ℕ, (∑ d ∈ n.divisors,
            ((if ((n / d : ℕ) : ZMod N) = a then (d : ℂ) ^ (k - 1) else 0) +
              (if ((n / d : ℕ) : ZMod N) = -a then (d : ℂ) ^ (k - 1) else 0))) *
          Complex.exp (2 * π * Complex.I * z) ^ n := by sorry
