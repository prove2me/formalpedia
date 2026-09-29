-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_sub_algebraMap_evalAt_eq_one_of_derivative_evalEval_ne_zero_of_ord_sub_algebraMap_evalAt_eq_one
-- name    : AlgebraicCurve.Place.ord_sub_algebraMap_evalAt_eq_one_of_derivative_evalEval_ne_zero_of_ord_sub_algebraMap_evalAt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/78734dc9-47d2-5fc1-8b66-9259395d714e
-- title:
--   Transfer of a uniformiser across a separable plane relation
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal{O}_v \subsetneq F$ containing the image of $K$ and which is a principal ideal ring; write $\operatorname{ord}_v(f) = -\log$ of the associated $\mathbb{Z}^{m0}$-valued adic valuation of $f$. Assume $v$ is rational, meaning that $K \to \mathcal{O}_v/\mathfrak{m}_v$ is surjective, and for $f \in \mathcal{O}_v$ write $f(v) \in K$ for the value `v.evalAt f`, a chosen preimage in $K$ of the residue of $f$ (and $0$ for $f \notin \mathcal{O}_v$). Let $z \in \mathcal{O}_v$ and $y \in F$, and let $G$ be a polynomial in $K[Z][Y]$, the inner variable being $Z$ and the outer $Y$. Suppose that $G$, with its coefficients pushed into $F$, vanishes at $(z,y)$; that $\partial G/\partial Y$, the derivative in the outer variable, has $(\partial G/\partial Y)(z(v), y(v)) \neq 0$ in $K$; and that $\operatorname{ord}_v\bigl(y - y(v)\bigr) = 1$. Then $\operatorname{ord}_v\bigl(z - z(v)\bigr) = 1$. Membership of $y$ in $\mathcal{O}_v$ is not assumed; it is forced by the hypothesis on $\operatorname{ord}_v(y - y(v))$.
--
--   This is the transfer of a uniformiser along a plane relation at a point where the relation is separable in the second variable: if $y - y(v)$ generates the maximal ideal at a rational place $v$ and the partial derivative $\partial G/\partial Y$ does not vanish at the residue point, then the other coordinate $z$ also yields a uniformiser $z - z(v)$. It is used in the construction of local charts on modular curves, in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot), to pass from a uniformiser supplied by a projective coordinate to one in the chart coordinate; the proof cites the factorisation $y - y(v) = h \cdot (z - z(v))$ with $h \in \mathcal{O}_v$ together with non-negativity of $\operatorname{ord}_v$ on $\mathcal{O}_v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_sub_algebraMap_evalAt_eq_one_of_derivative_evalEval_ne_zero_of_ord_sub_algebraMap_evalAt_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.ord_sub_algebraMap_evalAt_eq_one_of_derivative_evalEval_ne_zero_of_ord_sub_algebraMap_evalAt_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F} (hz : z ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0)
    (hy1 : v.ord (y - algebraMap K F (v.evalAt y)) = 1) :
    v.ord (z - algebraMap K F (v.evalAt z)) = 1 := by sorry
