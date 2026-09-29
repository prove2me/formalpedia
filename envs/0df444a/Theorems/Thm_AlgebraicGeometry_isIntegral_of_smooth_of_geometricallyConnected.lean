-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected
-- name    : AlgebraicGeometry.isIntegral_of_smooth_of_geometricallyConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/a9b33b12-4c24-55dc-81d0-bb4e80583726
-- title:
--   Smooth geometrically connected pointed scheme over ̄ k is integral
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme, and let $t : X \to \operatorname{Spec} k$ be a morphism of schemes (all in a single universe, with $\operatorname{Spec} k$ formed from the commutative ring $k$). Assume that $t$ is smooth, that $t$ satisfies `GeometricallyConnected`, and that $t$ admits a section, i.e. there is a morphism $e : \operatorname{Spec} k \to X$ with $e$ followed by $t$ equal to the identity of $\operatorname{Spec} k$. The conclusion is that $X$ is integral in Mathlib's sense, `IsIntegral X`: the underlying space of $X$ is nonempty and, for every nonempty open subset $U$ of $X$, the ring of sections $\mathcal{O}_X(U)$ is an integral domain. Thus the statement is about the absolute scheme $X$, not about relative properties of $t$: smoothness and geometric connectedness of the structure morphism over an algebraically closed base, together with the existence of a $k$-rational point supplied by $e$, force $X$ to be irreducible and reduced.
--
--   This is the standard fact that a smooth, geometrically connected scheme over an algebraically closed field which carries a rational point is integral. It is applied in this development to Jacobians and other pointed smooth group schemes over an algebraically closed field, for instance in the relative Picard constructions that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_of_smooth_of_geometricallyConnected
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    (hsm : Smooth t) (hgc : GeometricallyConnected t)
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ t = 𝟙 _) :
    IsIntegral X := by sorry
