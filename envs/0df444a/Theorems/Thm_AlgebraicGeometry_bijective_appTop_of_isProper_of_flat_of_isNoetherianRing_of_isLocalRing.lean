-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
-- name    : AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/c7acab97-f74c-5663-86a8-f3422d7bec20
-- title:
--   Degree-zero base change over a Noetherian local base
-- statement:
--   Let $A$ be a commutative ring that is Noetherian and local, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal A`, let $X$ be a scheme (both in the same universe), and let $p \colon X \to \operatorname{Spec} A$ be a morphism that is proper and flat. Form the closed fibre as the pullback of $p$ along $\operatorname{Spec}$ of the quotient homomorphism $A \to A/\mathfrak m$, and let $\mathrm{pr}_2$ be the projection of this pullback to $\operatorname{Spec}(A/\mathfrak m)$. The hypothesis is that the map induced by $\mathrm{pr}_2$ on global sections of the structure sheaves, i.e. the ring homomorphism $A/\mathfrak m \to \Gamma(X_0, \mathcal O_{X_0})$ given by `appTop`, is bijective as a function. The conclusion is that the corresponding map for $p$ itself, the ring homomorphism $A \to \Gamma(X, \mathcal O_X)$ given by `p.appTop`, is bijective as a function.
--
--   This is the local form, over a Noetherian local base, of Grothendieck's theorem on cohomology and base change in degree zero for proper flat morphisms: the condition that the closed fibre have only constant global functions propagates to the whole base. It is used in the project to obtain the corresponding statement under finite presentation hypotheses, the version over a locally Noetherian base formulated fibrewise over residue fields, and a rigidity statement for group laws over Artinian rings in the study of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop := by sorry
