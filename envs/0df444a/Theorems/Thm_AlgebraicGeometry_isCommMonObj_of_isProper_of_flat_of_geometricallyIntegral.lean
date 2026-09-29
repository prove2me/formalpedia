-- Prove2me | Theorems.Thm_AlgebraicGeometry_isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
-- name    : AlgebraicGeometry.isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/b0e75e00-f3b9-53dc-96f7-6405833e759a
-- title:
--   Proper flat geometrically integral group schemes are commutative
-- statement:
--   Let $R$ be a commutative ring and let $G$ be an object of the category $\mathrm{Over}\,(\operatorname{Spec} R)$, that is a scheme together with a structure morphism `G.hom` to $\operatorname{Spec} R$. Assume that `G.hom` is proper, flat, locally of finite presentation and geometrically integral, and that $G$ carries a group-object structure `GrpObj G` for the cartesian monoidal structure on $\mathrm{Over}\,(\operatorname{Spec} R)$ (so a multiplication $G\times_R G\to G$, a unit section $\eta[G]\colon \operatorname{Spec} R\to G$ and an inversion, satisfying the group axioms, all over $\operatorname{Spec} R$). The conclusion is `IsCommMonObj G`: the underlying monoid object is commutative, i.e. the multiplication is unchanged by composing with the braiding of $G\times_R G$, equivalently the commutator morphism $G\times_R G\to G$ equals the composite of the terminal map $G\times_R G\to\operatorname{Spec} R$ with the unit section. No separate abelian-ness or connectedness hypothesis beyond geometric integrality of the structure morphism is required.
--
--   This is the classical statement that abelian schemes are commutative, here over an arbitrary commutative base ring $R$, extending the version over a field in which properness alone suffices. It supplies commutativity of the relative group law on a Weierstrass projective model, via [`WeierstrassProjModel.RelativeGroupLaw.mul_comm_of_forall_field_mul_comm`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_comm_of_forall_field_mul_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u

theorem AlgebraicGeometry.isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
    {R : Type u} [CommRing R]
    (G : Over (Spec (CommRingCat.of R))) [IsProper G.hom] [Flat G.hom]
    [LocallyOfFinitePresentation G.hom] [GeometricallyIntegral G.hom] [GrpObj G] :
    IsCommMonObj G := by sorry
