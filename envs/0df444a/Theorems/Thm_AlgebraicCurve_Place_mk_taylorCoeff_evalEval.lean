-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_evalEval
-- name    : AlgebraicCurve.Place.mk_taylorCoeff_evalEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/467cbf99-28bf-5ea6-bd69-093c6045bb57
-- title:
--   Taylor expansion commutes with bivariate polynomial evaluation
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Assume $v$ is rational, meaning that the composite $K \to \mathcal{O}_v \to \mathcal{O}_v/\mathfrak{m}_v$ onto the residue field is surjective. Let $t \in F$ satisfy $\operatorname{ord}_v t = 1$, where $\operatorname{ord}_v$ is minus the logarithm of the associated $\mathbb{Z}^{\mathrm{m}0}$-valued adic valuation, and let $z, y \in \mathcal{O}_v$. For $f \in F$ and $r \in \mathbb{N}$, the coefficient $a_r(f) =$ `taylorCoeff v t r f` $\in K$ is obtained by applying the residue evaluation `evalAt` to the $r$-th iterate of $f \mapsto (f - \operatorname{evalAt}(f)) t^{-1}$ started at $f$. Then for every $G \in K[Z][Y]$ the power series $\sum_n a_n\bigl(G(z,y)\bigr) T^n \in K[[T]]$, where $G$ is evaluated in $F$ after mapping its coefficients along $K \to F$ (the inner variable at $z$, the outer at $y$), equals $G$ with coefficients mapped along $K \to K[[T]]$ and evaluated at the two power series $\sum_n a_n(z) T^n$ and $\sum_n a_n(y) T^n$.
--
--   This is the formal statement that expanding an algebraic relation in a local parameter is legitimate: the Taylor map $\mathcal{O}_v \to K[[T]]$, $f \mapsto \sum_n a_n(f) T^n$, is a $K$-algebra homomorphism, so polynomial identities over $K$ between elements of $\mathcal{O}_v$ pass to their expansions. It is used when expanding the equation of a curve at a rational place, for instance in the construction of formal local solutions and in the uniqueness of such expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mk_taylorCoeff_evalEval.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.mk_taylorCoeff_evalEval
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K)) :
    (PowerSeries.mk fun n =>
        taylorCoeff v t n ((G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y))
      = (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.mk fun n => taylorCoeff v t n z) (PowerSeries.mk fun n => taylorCoeff v t n y) := by sorry
