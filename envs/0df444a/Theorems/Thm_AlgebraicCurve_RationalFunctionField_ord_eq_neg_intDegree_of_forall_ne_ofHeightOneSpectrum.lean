-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
-- name    : AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/aff2c448-5247-5cf8-b286-350bd75e11e5
-- title:
--   At the infinite place of K(X), ord = -deg
-- statement:
--   Let $K$ be a field and let $v$ be a place of the rational function field $\mathrm{RatFunc}\ K$ over $K$ in the sense of the project's structure `Place`: a valuation subring of $\mathrm{RatFunc}\ K$ that contains the image of $K$ under the structure map, is not the whole field, and is a principal ideal ring. Assume that $v$ is distinct from `Place.ofHeightOneSpectrum w` for every $w$ in the height-one spectrum of the polynomial ring $K[X]$, i.e. $v$ is not the place whose valuation subring is that of the $w$-adic valuation on $\mathrm{RatFunc}\ K$, for any nonzero prime $w$ of $K[X]$. Let $f \neq 0$ be a rational function. Then $v.\mathrm{ord}\, f = -f.\mathrm{intDegree}$, where $v.\mathrm{ord}\, f$ is minus the logarithm (in $\mathbb{Z}$, via `WithZero.log`) of the value at $f$ of the adic valuation attached to the maximal ideal of the valuation ring of $v$, viewed as a point of the height-one spectrum, and $f.\mathrm{intDegree}$ is the degree of the numerator of $f$ minus the degree of its denominator.
--
--   This identifies the unique place of $K(X)/K$ that is not a finite place — the place at infinity — and computes its order function as minus the degree, the divisor-theoretic form of the statement that $1/X$ is a uniformiser at infinity. It is used in the study of places and divisors of function fields, for instance in showing that a place of a function field over an algebraically closed field with all orders zero forces membership in the constants, and that a rational function with prescribed orders has degree zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) {f : RatFunc K} (hf : f ≠ 0) : v.ord f = -f.intDegree := by sorry
