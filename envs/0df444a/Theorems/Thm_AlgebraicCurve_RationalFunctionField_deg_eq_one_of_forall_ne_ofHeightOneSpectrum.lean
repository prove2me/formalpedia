-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
-- name    : AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/b6d8765a-04bc-52eb-8cf3-5bdc073cf866
-- title:
--   The place at infinity of K(t) has degree one
-- statement:
--   Let $K$ be a field and let $v$ be a place of the rational function field $\mathrm{RatFunc}\,K$ over $K$ in the sense of the project's structure `Place`: a valuation subring of $\mathrm{RatFunc}\,K$ which contains the image of $K$ under the structure map, is not the whole field, and is a principal ideal ring. Assume that $v$ differs from `Place.ofHeightOneSpectrum w` for every $w$ in the height-one spectrum of the polynomial ring $K[X]$, that is, $v$ is not the place whose valuation subring is the valuation subring of the $w$-adic valuation of $\mathrm{RatFunc}\,K$ attached to a nonzero prime ideal $w$ of $K[X]$. Then $v.\mathrm{deg} = 1$, where $v.\mathrm{deg}$ is defined as the $K$-dimension $\operatorname{finrank}_K$ of the residue field of the local ring $v.\mathrm{toValuationSubring}$; equivalently, the structure map $K \to \kappa(v)$ is an isomorphism.
--
--   This is the classical computation that the place at infinity of the rational function field $K(t)$ — the unique place of $K(t)/K$ that is not one of the finite places coming from the nonzero primes of $K[X]$ — has residue degree one, the residue field being $K$ itself. It feeds the degree theory of divisors on the rational function field and is used by the statements that places have nonzero degree, that the place at infinity has degree one, and that divisors built from orders at the finite places have degree zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.deg = 1 := by sorry
