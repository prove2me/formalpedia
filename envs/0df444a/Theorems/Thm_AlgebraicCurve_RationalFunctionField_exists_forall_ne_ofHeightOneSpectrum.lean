-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
-- name    : AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/5e0bdace-46ac-5793-8044-fe6a2fce8738
-- title:
--   Existence of a place of K(t)/K that is not a finite place
-- statement:
--   Let $K$ be a field and let $\mathrm{RatFunc}\,K$ be the rational function field in one variable over $K$. A `Place K (RatFunc K)` consists of a valuation subring $\mathcal{O}$ of $\mathrm{RatFunc}\,K$ such that the image of every element of $K$ under the structure map $K \to \mathrm{RatFunc}\,K$ lies in $\mathcal{O}$, such that $\mathcal{O} \neq \top$, and such that $\mathcal{O}$ is a principal ideal ring; for a height-one prime $w$ of the polynomial ring $K[X]$, the place `Place.ofHeightOneSpectrum w` is the one whose valuation subring is the valuation subring of the $w$-adic valuation of $\mathrm{RatFunc}\,K$ (regarded as the fraction field of $K[X]$), the three defining conditions holding because $w$-adic valuations are $\le 1$ on polynomials, are nontrivial, and have principal-ideal valuation subrings. The theorem asserts: there exists a place $v$ of $K(t)$ over $K$ in this sense such that for every height-one prime $w$ of $K[X]$ one has $v \neq$ `Place.ofHeightOneSpectrum w`. No hypotheses beyond $K$ being a field are imposed.
--
--   This is the existence half of the classification of the places of the projective line: besides the finite places, attached to the height-one primes of $K[X]$, there is the place at infinity. It is used in the development of places and orders on a rational function field, for instance in the results on elements with a pole at some place, on elements regular at every place, and on degrees of divisors of rational functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] : ∃ v : Place K (RatFunc K), ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w := by sorry
