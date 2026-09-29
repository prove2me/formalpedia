-- Prove2me | Theorems.Thm_FormalGroup_exists_nthSeries_eq_smul_add_sq_mul
-- name    : FormalGroup.exists_nthSeries_eq_smul_add_sq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/ebbbc6a9-ad57-5414-a4dd-b45c43ac15c3
-- title:
--   [n](T) = nT + T²G(T) for formal group n-series
-- statement:
--   Let $R$ be a commutative ring and let $F$ be a one-dimensional formal group law over $R$, so that `F.toPowerSeries` is a two-variable power series over $R$ satisfying the group-law axioms. For a natural number $n$, the $n$-th series `F.nthSeries n` is defined by recursion: the $0$-th series is $0$, and the $(n+1)$-st series is obtained by substituting the pair consisting of `F.nthSeries n` and the variable $X$ into the group law $F$. The theorem asserts that for every such $R$, every $F$ and every $n : \mathbb{N}$ there exists a one-variable power series $G \in R[[X]]$ with $$\mathtt{F.nthSeries } n = (n : R) \cdot X + X^2 G,$$ where $(n : R)$ denotes the image of $n$ under the canonical map $\mathbb{N} \to R$ acting by scalar multiplication on $X$. In other words, the multiplication-by-$n$ series of $F$ has zero constant term, linear coefficient equal to the image of $n$ in $R$, and an unspecified remainder divisible by $X^2$.
--
--   This is the standard expansion $[n](T) = nT + O(T^2)$ of the multiplication-by-$n$ endomorphism of a one-dimensional formal group law. It is the form in which the estimate for $[n]$ on topologically nilpotent points is used; it feeds the analysis of $n$-torsion in [`FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_nthSeries_eq_smul_add_sq_mul.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FormalGroup.exists_nthSeries_eq_smul_add_sq_mul {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    ∃ G : PowerSeries R, F.nthSeries n = (n : R) • PowerSeries.X + PowerSeries.X ^ 2 * G := by sorry
