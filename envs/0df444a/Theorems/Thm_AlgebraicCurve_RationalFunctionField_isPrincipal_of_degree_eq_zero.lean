-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
-- name    : AlgebraicCurve.RationalFunctionField.isPrincipal_of_degree_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/11a5bf47-ef05-59a7-b1aa-cd6f5e51e684
-- title:
--   Degree-zero divisors on P¹ are principal
-- statement:
--   Let $K$ be a field and let $F = \mathrm{RatFunc}\,K$ be the field of rational functions in one variable over $K$. A place of $F$ over $K$ is, in the sense of this development, a valuation subring of $F$ that contains $\operatorname{algebraMap} K F(a)$ for every $a \in K$, is not the whole of $F$, and is a principal ideal ring; a divisor is a finitely supported function $D$ from the places of $F$ over $K$ to $\mathbb{Z}$. The hypothesis is that the degree of $D$ vanishes, the degree being the additive extension of $v \mapsto D(v)\cdot \deg v$, i.e. $\sum_{v \in \operatorname{supp} D} D(v)\,\deg v = 0$, where $\deg v$ is the residue degree attached to the place $v$ by `Place.deg`. The conclusion is that $D$ is principal in the sense of the project predicate `Divisor.IsPrincipal`: there exists $f \in F$ with $f \neq 0$ and $D(v) = \operatorname{ord}_v(f)$ for every place $v$ of $F$ over $K$, where $\operatorname{ord}_v$ is the order function `Place.ord` attached to $v$.
--
--   This is the statement that the divisor class group of degree zero of the projective line over $K$ vanishes, i.e. that the rational function field has genus zero in the divisor-theoretic sense. It is used in the computation of the Riemann–Roch difference $\ell(D) - \ell(K-D)$ for $\mathbb{P}^1$ ([`AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero`](thm.html#AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero)) and, transported along a suitable identification, in the genus-zero case for modular curves ([`ModularCurve.isPrincipal_of_degree_eq_zero_charLOne`](thm.html#ModularCurve.isPrincipal_of_degree_eq_zero_charLOne)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.isPrincipal_of_degree_eq_zero {K : Type*} [Field K] (D : Divisor K (RatFunc K)) (hD : Divisor.degree D = 0) : D.IsPrincipal := by sorry
