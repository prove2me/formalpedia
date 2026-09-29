-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
-- name    : AlgebraicCurve.Place.eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/b20eb5cc-59d9-58fe-a2cc-2795f9607199
-- title:
--   Uniqueness of the formal branch through a simple root
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, let $L$ be a field and $\iota : K \to L$ a ring homomorphism. Let $v$ be a place of $F/K$, i.e. a valuation subring $\mathcal{O}_v \subsetneq F$ containing $\operatorname{image}(K \to F)$ and which is a principal ideal ring, and assume $v$ is rational in the sense that $K \to \mathcal{O}_v/\mathfrak m_v$ is surjective; for $f \in \mathcal{O}_v$ write $f(v) := \mathrm{evalAt}_v(f) \in K$ for the element of $K$ obtained from the residue of $f$ through a fixed section of this surjection (and $0$ for $f \notin \mathcal{O}_v$). Let $z, y \in \mathcal{O}_v$ with $\operatorname{ord}_v(z - z(v)) = 1$, where $\operatorname{ord}_v$ is minus the logarithm of the associated height-one-spectrum valuation. Let $G \in K[Z][Y]$ satisfy $G(z,y) = 0$ in $F$ (coefficients pushed into $F$, $Z \mapsto z$ the inner and $Y \mapsto y$ the outer variable) and $(\partial G/\partial Y)(z(v), y(v)) \neq 0$ in $K$, the derivative being taken in the outer variable. Finally let $Y \in L[[T]]$ have constant coefficient $\iota(y(v))$ and satisfy $G^{\iota}(\iota(z(v)) + T,\, Y) = 0$, where $G^{\iota}$ has coefficients mapped into $L[[T]]$ by $\iota$ followed by the constant-series map. Then $Y$ is the image under $\iota$ of $\sum_{n \ge 0} a_n T^n$, where $a_n = \mathrm{taylorCoeff}_v(t, n, y)$ with $t = z - z(v)$, defined by $a_n = r_n(v)$ for the remainders $r_0 = y$, $r_{n+1} = (r_n - r_n(v))\,t^{-1}$.
--
--   This identifies the formal branch of the curve $G = 0$ through the $K$-rational point $(z(v), y(v))$ with the image of the Taylor expansion of $y$ in the local parameter $z - z(v)$ at $v$: after any extension of scalars $\iota$, a power-series solution with the prescribed constant term is unique. It is used to produce power-series charts, via [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] {L : Type*} [Field L] (ι : K →+* L)
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0)
    (Y : PowerSeries L) (hY0 : PowerSeries.constantCoeff Y = ι (v.evalAt y))
    (hY : (G.map (Polynomial.mapRingHom (PowerSeries.C.comp ι))).evalEval
        (PowerSeries.C (ι (v.evalAt z)) + PowerSeries.X) Y = 0) :
    Y = PowerSeries.map ι
          (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) := by sorry
