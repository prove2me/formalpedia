-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf
-- name    : AlgebraicGeometry.Scheme.Opens.range_algebraMap_functionField_eq_iInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/01f7f5b0-88ea-5957-8757-35a2d3049e01
-- title:
--   Sections on U are the rational functions regular on U
-- statement:
--   Let $X$ be an integral scheme (in particular irreducible, so it has a generic point and a function field $K(X)$, the stalk of $\mathcal{O}_X$ there), and let $U$ be an open subset of $X$ which is assumed nonempty as a subtype. The canonical maps $\Gamma(X,U)\to K(X)$ and, for each point $x$, $\mathcal{O}_{X,x}\to K(X)$ are the algebra maps coming from the algebra structures on $K(X)$ over sections and over stalks. The assertion is an equality of subrings of $K(X)$: the range of $\operatorname{algebraMap}\,\Gamma(X,U)\,K(X)$ equals the infimum, taken in the lattice of subrings of $K(X)$, of the ranges of $\operatorname{algebraMap}\,\mathcal{O}_{X,x}\,K(X)$ over all points $x$ of $X$ together with a proof that $x\in U$; that is, the image of $\Gamma(X,U)$ in $K(X)$ is the intersection $\bigcap_{x\in U}\mathcal{O}_{X,x}$ of the images of the local rings at the points of $U$. No Noetherian, separatedness, finiteness or dimension hypothesis is imposed.
--
--   This is the standard identification, on an integral scheme, of the sections of $\mathcal{O}_X$ over an open $U$ with the rational functions regular at every point of $U$, extending the affine statement [`AlgebraicGeometry.IsAffineOpen.range_algebraMap_functionField_eq_iInf`](thm.html#AlgebraicGeometry.IsAffineOpen.range_algebraMap_functionField_eq_iInf) to arbitrary opens. It is used in the treatment of algebraic curves, in [`AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset`](thm.html#AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset) and [`AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite`](thm.html#AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.Scheme.Opens.range_algebraMap_functionField_eq_iInf
    {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U] :
    (algebraMap Γ(X, U) X.functionField).range =
      ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by sorry
