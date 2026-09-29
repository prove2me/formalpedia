-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
-- name    : AlgebraicCurve.RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/6909b602-2efa-5ea4-b2ec-e54556b62997
-- title:
--   At most one place of K(t)/K is not finite
-- statement:
--   Let $K$ be a field, and consider the rational function field $\mathrm{RatFunc}\,K$ in one variable over $K$. Here a place of $\mathrm{RatFunc}\,K$ over $K$, i.e. an element of `Place K (RatFunc K)`, is by definition a valuation subring $\mathcal O$ of $\mathrm{RatFunc}\,K$ such that the image of every element of $K$ under the structure map $K \to \mathrm{RatFunc}\,K$ lies in $\mathcal O$, such that $\mathcal O \neq \mathrm{RatFunc}\,K$, and such that $\mathcal O$ is a principal ideal ring. For a height-one prime $w$ of the polynomial ring $K[X]$, the place `Place.ofHeightOneSpectrum w` is the valuation subring of the $w$-adic valuation of $\mathrm{RatFunc}\,K$ (the fraction field of $K[X]$). The assertion is that the set of those places $v$ of $\mathrm{RatFunc}\,K$ over $K$ with $v \neq$ `Place.ofHeightOneSpectrum w` for every height-one prime $w$ of $K[X]$ is a subsingleton: any two such places coincide. The statement is the uniqueness half only; no place at infinity is named, and the existence of a non-finite place is not part of the conclusion.
--
--   This is the uniqueness part of Ostrowski's classification of the places of the rational function field: the closed points of $\mathbb A^1_K$, i.e. the height-one primes of $K[X]$, account for all places of $K(t)/K$ except at most one, the place at infinity. It is used in the treatment of divisors on $\mathbb P^1_K$, for instance in [`AlgebraicCurve.Place.finite_setOf_deg_eq`](thm.html#AlgebraicCurve.Place.finite_setOf_deg_eq), [`AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed`](thm.html#AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed) and [`AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap`](thm.html#AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] : {v : Place K (RatFunc K) | ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w}.Subsingleton := by sorry
