-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum
-- name    : AlgebraicCurve.Divisor.correspondence_single_one_apply_eq_sum_and_eq_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/dfddc3e8-1f31-59eb-adad-07bd487b3d0f
-- title:
--   Coefficient of the correspondence ψ_*φ^* at a single place
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and suppose $F'$ satisfies `HasPrincipalDivisors K F'`: every nonzero $f \in F'$ has a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ for every place $v$ of $F'$ over $K$ and $\deg D = 0$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and a divisor is a finitely supported function from places to $\mathbb{Z}$. Let $\varphi, \psi \colon F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, and let $x, y$ be places of $F$ over $K$. The correspondence $T = \psi_* \circ \varphi^*$ on divisors of $F$ is the composite of pull-back along $\varphi$ and push-forward along $\psi$, taken for the $F$-algebra structures on $F'$ induced by $\varphi$ and $\psi$. The conclusion is the conjunction of two evaluations of $T$ at the divisor $1\cdot[x]$, read off at $y$: first, $T(1\cdot[x])(y)$ equals the sum over the finite fibre of places $W$ of $F'$ restricting to $x$ along $\varphi$ of $e(W/\varphi)\, f(W/\psi)$ when the restriction of $W$ along $\psi$ is $y$ and of $0$ otherwise; second, $T(1\cdot[x])(y)$ equals the `finsum` over all places $W$ of $F'$ of the same product, cut off by the conjunction that $W$ restricts to $x$ along $\varphi$ and to $y$ along $\psi$. Here $e(W/\varphi)$ is the infimum of the positive integers of the form $\operatorname{ord}_W(\varphi(f))$ with $f \in F$ nonzero, and $f(W/\psi)$ is the inertia degree of $W$ over its $\psi$-restriction.
--
--   This is the coefficient form, at a single place, of the divisor-level formula $\psi_*\varphi^*[x] = \sum_{W \mid x} e(W/\varphi) f(W/\psi)\,[\,W|_\psi\,]$ for a correspondence between function fields. The second, `finsum`, shape is the one used to define place-counting matrices, so that an entry of such a matrix can be identified with a correspondence coefficient and then evaluated by the first, finite-sum, shape; it is used in the Čerednik–Drinfel'd moduli-tower computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Classical

theorem AlgebraicCurve.Divisor.correspondence_single_one_apply_eq_sum_and_eq_finsum
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (x y : Place K F) :
    (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0) ∧
    (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0) := by sorry
