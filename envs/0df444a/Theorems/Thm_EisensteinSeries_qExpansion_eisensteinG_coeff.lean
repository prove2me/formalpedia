-- Prove2me | Theorems.Thm_EisensteinSeries_qExpansion_eisensteinG_coeff
-- name    : EisensteinSeries.qExpansion_eisensteinG_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/7770826f-045e-5a13-95de-30e4d07d530f
-- title:
--   q_N-expansion of the level-N Eisenstein series G_kᵃ
-- statement:
--   Let $N\ge 1$, let $k$ be a natural number with $3\le k$, let $a=(a_0,a_1)\in(\mathbb Z/N\mathbb Z)^2$, and let $n\ge 0$. Consider the Eisenstein series $G^a_{N,k}$ of weight $k$ attached to the congruence class $a$, defined on the upper half-plane by the sum $\sum_v \mathrm{eisSummand}\,k\,v\,z$ over all $v\colon \mathrm{Fin}\,2\to\mathbb Z$ whose reduction modulo $N$ is $a$, i.e. $\sum_{v\equiv a\ (N)}(v_0 z+v_1)^{-k}$. The assertion is an identity for the $n$-th coefficient of its width-$N$ $q$-expansion at $i\infty$ (in the variable $q_N=e^{2\pi i z/N}$). For $n=0$ the coefficient is $\sum_{d\equiv a_1\ (N)} (d^k)^{-1}$, the sum being over all integers $d$ congruent to $a_1$ modulo $N$ (the term $d=0$ contributing $0$), if $a_0=0$, and $0$ otherwise. For $n\ge 1$ it equals $$\frac{(-2\pi i)^k}{(k-1)!\,N^k}\sum_{m\mid n}m^{k-1}\Bigl(\bigl[\,n/m\equiv a_0\,\bigr]\,\psi(a_1 m)+(-1)^k\bigl[\,n/m\equiv -a_0\,\bigr]\,\psi(-a_1 m)\Bigr),$$ where $m$ runs over the positive divisors of $n$, the brackets are the indicator of the stated congruence in $\mathbb Z/N\mathbb Z$, and $\psi$ is the standard additive character $x\mapsto e^{2\pi i x/N}$ of $\mathbb Z/N\mathbb Z$.
--
--   This is the classical Fourier expansion of the congruence-class Eisenstein series of level $\Gamma(N)$ and weight $k\ge 3$: constant term a partial zeta value, higher coefficients twisted divisor sums with values in $\frac{(-2\pi i)^k}{(k-1)!N^k}\mathbb Z[\zeta_N]$. It underlies the construction of weight-three modular forms on $\Gamma_1(N)$ with prescribed integral $q$-expansions and prescribed behaviour under slash operators, used in the Siegel-unit part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_qExpansion_eisensteinG_coeff.lean

import Mathlib
import Definitions.Def_EisensteinSeries_EisensteinG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Real Complex
open scoped Nat

theorem EisensteinSeries.qExpansion_eisensteinG_coeff (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) (n : ℕ) :
    (UpperHalfPlane.qExpansion N (EisensteinSeries.eisensteinG N k a)).coeff n =
      if n = 0 then
        (if a 0 = 0 then ∑' d : {d : ℤ // (d : ZMod N) = a 1}, ((d : ℂ) ^ k)⁻¹ else 0)
      else
        (-2 * π * I) ^ k / ((k - 1)! * (N : ℂ) ^ k) *
          ∑ m ∈ n.divisors,
            ((if ((n / m : ℕ) : ZMod N) = a 0 then ZMod.stdAddChar (a 1 * (m : ZMod N)) else 0) +
              (-1) ^ k *
                (if ((n / m : ℕ) : ZMod N) = -a 0 then ZMod.stdAddChar (-(a 1 * (m : ZMod N))) else 0)) *
            (m : ℂ) ^ (k - 1) := by sorry
