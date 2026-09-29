-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero
-- name    : AlgebraicCurve.Place.mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/f392ca7b-0287-5103-aa56-5b9f33362d5f
-- title:
--   Regularity of roots of a plane relation at rational places
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project: a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, i.e. the composite $K \to \mathcal O_v \to \mathcal O_v/\mathfrak m_v$ into the residue field is surjective; for $f \in \mathcal O_v$ write $f(v) =$ `v.evalAt f` $\in K$ for the element of $K$ chosen by a fixed right inverse of that surjection as a preimage of the residue of $f$ (and $0$ for $f \notin \mathcal O_v$). Let $z \in \mathcal O_v$ and $y \in F$, and let $G \in K[Z][Y]$ be a polynomial in $Y$ with coefficients in $K[Z]$. Suppose that, after pushing the coefficients forward along $K \to F$, one has $G(z,y) = 0$ in $F$, the inner variable being evaluated at $z$ and the outer at $y$. Suppose further that the leading coefficient of $G$ as a polynomial in $Y$, an element of $K[Z]$, does not vanish at $z(v)$. Then $y \in \mathcal O_v$. (In particular the hypothesis on the leading coefficient forces $G \neq 0$.)
--
--   This is the algebraic regularity step for the dependent coordinate of a plane model: away from the zeros of the leading coefficient in $Y$, every root in $F$ of $G(z,\cdot)$ lies in the valuation ring of any rational place at which $z$ does, so that its value at the place is defined. It is used by [`AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne`](thm.html#AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne) and its separable variant, where non-vanishing of the $Y$-derivative at a place is deduced from a simplicity condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F} (hz : z ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hlead : G.leadingCoeff.eval (v.evalAt z) ≠ 0) :
    y ∈ v.toValuationSubring := by sorry
