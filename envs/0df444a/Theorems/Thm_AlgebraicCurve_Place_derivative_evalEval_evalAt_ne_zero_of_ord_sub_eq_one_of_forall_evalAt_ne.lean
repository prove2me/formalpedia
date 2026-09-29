-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
-- name    : AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/dd1c65d4-6d0a-5f46-beef-798d902a0b25
-- title:
--   Unramified, fibre-separating places give simple points of G
-- statement:
--   Let $K$ be a field of characteristic $0$ and $F$ a $K$-algebra which is a field, and suppose there is $x_0\in F$ with $F$ finite-dimensional over the intermediate field $K(x_0)$. Assume every place of $F$ over $K$ is rational, a place being a valuation subring of $F$ that contains $\operatorname{im}(K\to F)$, is not all of $F$ and is a principal ideal ring, and rationality meaning that $K$ surjects onto its residue field; for such a place $v$ and $f$ in its valuation ring, $v.\mathrm{evalAt}\,f\in K$ denotes the preimage of the residue of $f$ (and $0$ for $f$ outside the ring), while $v.\mathrm{ord}$ is the associated normalised integer valuation. Let $z\in F$ be transcendental over $K$, let $y\in F$, and let $G\in K[Z][Y]$ be irreducible with $G(z,y)=0$ after mapping the coefficients into $F[Z][Y]$. Let $Q$ be a place with $z,y$ in its valuation ring such that $\mathrm{ord}_Q\bigl(z-z(Q)\bigr)=1$, the leading coefficient of $G$ in $Y$ does not vanish at $z(Q)$, and $y$ separates $Q$ inside its fibre: every place $Q'\neq Q$ containing $z$ and $y$ with $z(Q')=z(Q)$ satisfies $y(Q')\neq y(Q)$. Then $\partial G/\partial Y$, the derivative in the outer variable, is non-zero at $\bigl(z(Q),y(Q)\bigr)$.
--
--   This is the classical passage from place-theoretic data on a function field of one variable — $z-z(Q)$ a uniformiser at $Q$, and $y$ injective on the fibre of $z$ through $Q$ — to the simple-point condition at $(z(Q),y(Q))$ on the plane curve cut out by $G$, argued by comparing the order of $z-z(Q)$ with the norm from $F$ to $K(z)$. It is used in the construction of local charts on the modular curve side, by [`ModularCurve.JZero.exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero`](thm.html#ModularCurve.JZero.exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero) and [`ModularCurve.JZero.exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero`](thm.html#ModularCurve.JZero.exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (hrat : ∀ w : Place K F, w.IsRational)
    {z y : F} (hz : Transcendental K z)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (Q : Place K F) (hzQ : z ∈ Q.toValuationSubring) (hyQ : y ∈ Q.toValuationSubring)
    (he : Q.ord (z - algebraMap K F (Q.evalAt z)) = 1)
    (hlead : G.leadingCoeff.eval (Q.evalAt z) ≠ 0)
    (hsep : ∀ Q' : Place K F, Q' ≠ Q → z ∈ Q'.toValuationSubring → Q'.evalAt z = Q.evalAt z →
      y ∈ Q'.toValuationSubring → Q'.evalAt y ≠ Q.evalAt y) :
    (Polynomial.derivative G).evalEval (Q.evalAt z) (Q.evalAt y) ≠ 0 := by sorry
