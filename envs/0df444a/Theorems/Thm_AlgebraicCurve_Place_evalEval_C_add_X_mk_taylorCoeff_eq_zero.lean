-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero
-- name    : AlgebraicCurve.Place.evalEval_C_add_X_mk_taylorCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/ba9241fd-429d-5f28-8849-72297ca40b25
-- title:
--   Formal Taylor branch satisfies the relation re-expanded at a place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F/K$ in the sense of the project, i.e. a valuation subring $\mathcal O_v \subseteq F$ containing $\operatorname{im}(K \to F)$, different from $F$ itself, and whose ideals are all principal. Assume $v$ is rational, meaning that $K \to \mathcal O_v/\mathfrak m_v$ is surjective, so that each $f \in \mathcal O_v$ has a residue value $v.\mathrm{evalAt}\, f \in K$ (a preimage of its residue class, and $0$ for $f \notin \mathcal O_v$). Let $z, y \in \mathcal O_v$, and suppose $t := z - \iota(v.\mathrm{evalAt}\, z)$ (where $\iota : K \to F$) satisfies $v.\mathrm{ord}\, t = 1$, the order being minus the logarithm of the $\mathbb Z^{m0}$-valued adic valuation attached to $v$; thus $t$ is a uniformiser at $v$. Let $G \in K[Z][Y]$ and assume that, after mapping its coefficients coefficientwise into $F$, the bivariate evaluation of $G$ at inner value $z$ and outer value $y$ vanishes in $F$, i.e. $G(z,y) = 0$. Then, after mapping the coefficients of $G$ coefficientwise into $K[[T]]$, the bivariate evaluation of $G$ at inner value $\mathrm{C}(v.\mathrm{evalAt}\, z) + T$ and outer value the power series $\sum_{n} \mathrm{taylorCoeff}\, v\, t\, n\, y \cdot T^n$ is $0$ in $K[[T]]$; here the $n$-th Taylor coefficient of $y$ is $v.\mathrm{evalAt}$ of the $n$-th remainder, the remainders being defined by $r_0 = y$ and $r_{n+1} = (r_n - \iota(v.\mathrm{evalAt}\, r_n))\, t^{-1}$.
--
--   This says that the formal branch $T \mapsto (z(v)+T, Y_v(T))$ obtained by Taylor expanding $z$ and $y$ at a rational place along the uniformiser $z - z(v)$ is a root of the defining relation $G$ re-expanded at the point $(z(v), y(v))$; no irreducibility, monicity or separability assumption is made on $G$. It underlies the later treatment of power series solutions at a place, being used for the uniqueness of such a branch and for the Taylor expansions of inverses and of general algebraic elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.evalEval_C_add_X_mk_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0) :
    (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C (v.evalAt z) + PowerSeries.X)
        (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) = 0 := by sorry
