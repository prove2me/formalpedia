-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing
-- name    : AutomorphicForm.GL2Twisted.ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/71801bc5-4ae7-5e5b-9359-4b4bacbf6df9
-- title:
--   Elliptic and split fibre pairings agree in bidegree (0,0)
-- statement:
--   Let $k$ be a natural number with $2 \le k$, and let $r, T$ be real numbers with $0 < r$ and $2r \le T$. The assertion is an identity of complex numbers between two integrals. On the left, $\theta$ runs over $[0,\pi]$ and the integrand is the elliptic fibre term of bidegree $(0,0)$ at level $T$, radius $r$ and angle $\theta$ — by definition $(4\pi \sin\theta/r)$ times the product of the bidegree-$(0,0)$ monomial factor, which is identically $1$, with the integral of $\cos^{0}\psi \sin^{0}\psi$ over $[-\Psi/2,\Psi/2]$ for $\Psi = \arccos\bigl((2r - T\cos\theta)/(T - 2r\cos\theta)\bigr)$, i.e. that arc length itself — multiplied by the value at $\cos\theta$ of the Chebyshev polynomial of the second kind of integer index $k-2$ over $\mathbb{R}$, coerced to $\mathbb{C}$. On the right, the factor $2\pi/r$ multiplies the integral over $t \in [-\operatorname{arcosh}(T/(2r)), \operatorname{arcosh}(T/(2r))]$ of $\exp(-(k-1)|t|)$ times the split fibre term of bidegree $(0,0)$ at level $T$ with arguments $r e^{t}$ and $r e^{-t}$, the latter being by definition the constant $\tfrac12 \cdot 1 \cdot 2\pi$.
--
--   This is the archimedean comparison, at the trivial bidegree $(0,0)$, between the angular pairing of the elliptic fibre data against the Chebyshev weight attached to the weight-$k$ discrete series and the hyperbolic pairing of the split fibre data against $e^{-(k-1)|t|}$, the substitution being $2r\cos\theta \leftrightarrow r(e^{t}+e^{-t})$ with $T/(2r) = \cosh(\operatorname{arcosh}(T/(2r)))$ marking the endpoint. It feeds the vanishing statement [`AutomorphicForm.GL2Twisted.exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero`](thm.html#AutomorphicForm.GL2Twisted.exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero), where the elliptic and split transforms are shown to pair to zero against the discrete series weights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing.lean

import Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Arcosh

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm.GL2Twisted Polynomial

theorem
AutomorphicForm.GL2Twisted.ellipticFibreTerm_pairing_eq_splitFibreTerm_pairing
    (k : ℕ) (hk : 2 ≤ k) (r T : ℝ) (hr : 0 < r) (hT : 2 * r ≤ T) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ellipticFibreTerm 0 0 T r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      (2 * Real.pi / r : ℂ) *
        ∫ t in (-Real.arcosh (T / (2 * r)))..Real.arcosh (T / (2 * r)),
          (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) * splitFibreTerm 0 0 T (r * Real.exp t) (r * Real.exp (-t)) := by sorry
