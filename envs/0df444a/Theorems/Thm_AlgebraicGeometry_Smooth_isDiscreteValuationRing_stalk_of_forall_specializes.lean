-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
-- name    : AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/4a6495b7-12e7-5c3f-955a-1b443fc3cb1a
-- title:
--   Smooth over a DVR: stalk at a generic point of the special fibre
-- statement:
--   Let $R$ be a commutative ring that is an integral domain and a discrete valuation ring, let $T$ be a scheme (in the same universe), and let $t \colon T \to \operatorname{Spec} R$ be a smooth morphism, where $\operatorname{Spec} R$ is the spectrum of $R$ viewed as an object of `CommRingCat`. Let $\eta$ be a point of $T$ whose image under the underlying continuous map of $t$ is the closed point of $\operatorname{Spec} R$, i.e. the point corresponding to the maximal ideal of $R$. Assume further that $\eta$ is, pointwise, a generic point of the special fibre: every point $y$ of $T$ such that $y$ specialises to $\eta$ (so $\eta$ lies in the closure of $\{y\}$) and such that $t$ maps $y$ to the closed point of $\operatorname{Spec} R$ is equal to $\eta$. The conclusion asserts the existence of a proof that the stalk $\mathcal{O}_{T,\eta}$ of the structure sheaf of $T$ at $\eta$ is an integral domain, together with the assertion, relative to that domain structure, that $\mathcal{O}_{T,\eta}$ is a discrete valuation ring; the existential packaging is needed because the predicate `IsDiscreteValuationRing` presupposes a domain instance.
--
--   This is the standard fact that on a scheme smooth over a discrete valuation ring, the generic points of the irreducible components of the special fibre are points of codimension one with discrete valuation local rings. It is used in the project as the local input for extension arguments in codimension one, notably in statements about sections of smooth morphisms and about valuation subrings attached to smooth curves of relative dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology

theorem AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ _ : IsDomain (T.presheaf.stalk η), IsDiscreteValuationRing (T.presheaf.stalk η) := by sorry
