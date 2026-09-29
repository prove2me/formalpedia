-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
-- name    : AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/ba5de16f-1086-5701-903d-c960fbd0bc4d
-- title:
--   Divisors cut out by a polynomial have degree zero
-- statement:
--   Let $K$ be a field and $q \in K[X]$ a polynomial. The assertion is about divisors of the rational function field $K(t) =$ `RatFunc K` over $K$, a divisor being a finitely supported function $D$ from the type `Place K (RatFunc K)` of places to $\mathbb{Z}$; here a place consists of a valuation subring of $K(t)$ that contains the image of $K$ under the structure map, is not all of $K(t)$, and is a principal ideal ring. For such a place $v$, $v.\mathrm{ord}(f)$ denotes $-\log$ of the value at $f$ of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height one prime of $v$, and the degree of a divisor is the finite sum $\sum_v D(v)\cdot v.\mathrm{deg}$, where $v.\mathrm{deg}$ is the degree attached to the place $v$ (a natural number, cast into $\mathbb{Z}$). The theorem states: for every divisor $D$ of $K(t)$ over $K$ such that $D(v) = v.\mathrm{ord}\bigl(\iota(q)\bigr)$ for every place $v$, where $\iota : K[X] \to K(t)$ is the structure map, the degree of $D$ is $0$. Nothing is claimed about the existence of such a $D$ for a given $q$.
--
--   This is the degree-zero property of principal divisors in the special case of the rational function field, for divisors coming from a polynomial: in classical terms, $\sum_v \operatorname{ord}_v(q)\deg(v) = 0$, the finite places contributing $\deg p$ for each irreducible factor $p$ and the place at infinity contributing $-\deg q$. It is used in the passage to arbitrary rational functions and in the vanishing of the sum of local residues over the finite places of $K(t)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap {K : Type*} [Field K] (q : Polynomial K) : ∀ D : Divisor K (RatFunc K), (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) → Divisor.degree D = 0 := by sorry
