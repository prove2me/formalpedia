-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
-- name    : AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/e04911ce-7b8e-5b0d-a191-ced04a147d0a
-- title:
--   Sections through closed-fibre points of étale morphisms over strictly henselian rings
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring and whose residue field $k = R/\mathfrak m$ is separably closed, let $X$ be a scheme (in the same universe as $R$), and let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is étale in the sense of the scheme-theoretic predicate `AlgebraicGeometry.Etale`. Let $x$ be a point of the underlying topological space of $X$ whose image under the continuous map underlying $f$ is the closed point of $\operatorname{Spec} R$, i.e. the prime corresponding to the maximal ideal of $R$. The assertion is that there exists a morphism of schemes $s \colon \operatorname{Spec} R \to X$ such that $s$ followed by $f$ is the identity morphism of $\operatorname{Spec} R$, so that $s$ is a section of $f$, and such that the point of $X$ obtained by applying the continuous map underlying $s$ to the closed point of $\operatorname{Spec} R$ is exactly $x$. Thus every point of the closed fibre of an étale morphism over a strictly henselian base is hit by a section.
--
--   This is the standard statement that over a strictly henselian local ring an étale morphism admits a section through any prescribed point of the closed fibre, the geometric counterpart of the lifting property of étale algebras over henselian rings. It is used in the project when producing integral points and torsion sections on models of modular curves over local bases, for instance by [`ModularCurve.XHDRModelAtP.exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart`](thm.html#ModularCurve.XHDRModelAtP.exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart) and [`ModularCurve.exists_integralPoints_through_of_torsion_over_p`](thm.html#ModularCurve.exists_integralPoints_through_of_torsion_over_p).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [AlgebraicGeometry.Etale f]
    (x : X) (hx : f.base x = IsLocalRing.closedPoint R) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x := by sorry
