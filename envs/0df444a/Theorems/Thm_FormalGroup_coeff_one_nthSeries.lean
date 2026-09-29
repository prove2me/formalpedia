-- Prove2me | Theorems.Thm_FormalGroup_coeff_one_nthSeries
-- name    : FormalGroup.coeff_one_nthSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/4208b44f-538f-5923-9ef6-41ecf140f30c
-- title:
--   Linear coefficient of the [n]-series equals n
-- statement:
--   Let $R$ be a commutative ring and let $F$ be an element of the project's structure `FormalGroup R` of one-dimensional formal group laws over $R$, whose underlying two-variable power series is `F.toPowerSeries`. For a natural number $n$, the power series `F.nthSeries n` in one variable is defined by recursion on $n$: `F.nthSeries 0` is the zero power series, and `F.nthSeries (n+1)` is obtained by substituting the pair of one-variable series $(\,$`F.nthSeries n`$,\,X)$, presented as the `Fin 2`-indexed family `![F.nthSeries n, PowerSeries.X]`, into `F.toPowerSeries`; thus it is the usual $[n]$-series, $[0](T)=0$ and $[n+1](T)=F([n](T),T)$. The theorem asserts that for every such $R$, $F$ and $n$ the coefficient of degree $1$ of `F.nthSeries n`, i.e. `PowerSeries.coeff 1 (F.nthSeries n)`, is equal to the image $(n : R)$ of $n$ under the canonical ring map $\mathbb{N}\to R$. No hypothesis beyond the formal group law axioms packaged in `FormalGroup R` is imposed; in particular $R$ need not be a domain or have any topology.
--
--   This is the standard statement $[n](T)=nT+O(T^2)$ for the multiplication-by-$n$ endomorphism of a one-dimensional formal group law, valid over an arbitrary commutative ring. It is used downstream in the analysis of the $n$-series of formal groups over complete local rings, for instance in the statements [`FormalGroup.IsDrinfeldBasisAdic.natCast_mem_pow`](thm.html#FormalGroup.IsDrinfeldBasisAdic.natCast_mem_pow) and [`FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete), and in comparing coefficients of the $n$-series with those of an invariant differential.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_coeff_one_nthSeries.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FormalGroup.coeff_one_nthSeries {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (F.nthSeries n) = (n : R) := by sorry
