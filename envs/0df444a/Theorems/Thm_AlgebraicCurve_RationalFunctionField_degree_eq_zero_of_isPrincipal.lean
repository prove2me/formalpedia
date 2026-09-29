-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_isPrincipal
-- name    : AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_isPrincipal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/7a4cdd94-6c35-5bc1-ba99-f621a042c600
-- title:
--   Principal divisors on K(t) have degree zero
-- statement:
--   Let $K$ be a field and let $F = \mathrm{RatFunc}\,K$ be the field of rational functions in one variable over $K$. A place of $F$ over $K$, in the sense used here, is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring; a divisor $D$ is a finitely supported function from the places of $F$ over $K$ to $\mathbb{Z}$, and its degree is the finite sum $\sum_v D(v)\cdot \deg v$, where $\deg v$ is the integer invariant `Place.deg` attached to $v$. The hypothesis is that $D$ is principal, i.e. that there exists $f \in \mathrm{RatFunc}\,K$ with $f \neq 0$ such that $D(v) = \mathrm{ord}_v(f)$ for every place $v$ of $\mathrm{RatFunc}\,K$ over $K$, where $\mathrm{ord}_v$ is the order function `Place.ord` of $v$. The conclusion is that $\mathrm{Divisor.degree}\,D = 0$.
--
--   This is the degree-zero statement for principal divisors, here for the rational function field $K(t)$ over an arbitrary base field $K$. It is used in the treatment of places of modular curves, via [`ModularCurve.placeSpecialization_exists_level_one_of_surjective`](thm.html#ModularCurve.placeSpecialization_exists_level_one_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_isPrincipal.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_isPrincipal {K : Type*} [Field K] {D : Divisor K (RatFunc K)} (hD : D.IsPrincipal) : Divisor.degree D = 0 := by sorry
