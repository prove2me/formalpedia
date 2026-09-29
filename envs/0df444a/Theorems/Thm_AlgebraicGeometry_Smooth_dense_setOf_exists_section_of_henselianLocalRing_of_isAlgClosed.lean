-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
-- name    : AlgebraicGeometry.Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/19d67077-de6f-5cab-ba83-bf582006806b
-- title:
--   Sections are dense in the special fibre of a smooth morphism
-- statement:
--   Let $R$ be a commutative ring in a fixed universe which is a henselian local ring and whose residue field $\mathrm{IsLocalRing.ResidueField}\,R$ is algebraically closed, let $T$ be a scheme, and let $t : T \to \operatorname{Spec} R$ be a morphism of schemes carrying a `Smooth` instance. Consider the special fibre as a topological space, namely the subtype of points $x$ of the underlying space of $T$ with $t(x)$ equal to the closed point $\mathrm{IsLocalRing.closedPoint}\,R$ of $\operatorname{Spec} R$, equipped with the subspace topology. The assertion is that the following subset of this subtype is dense: the set of those $x$ for which there exists a morphism $s : \operatorname{Spec} R \to T$ with $s$ followed by $t$ equal to the identity of $\operatorname{Spec} R$ — that is, a section of $t$ — such that the image of the closed point of $\operatorname{Spec} R$ under $s$ is the point $x$ of $T$ underlying the given element of the subtype. In words: the points of the special fibre which are specialisations of sections of $t$ are dense in the special fibre.
--
--   This is the density statement underlying the smoothening/Néron-model criterion: over a henselian local ring with algebraically closed residue field, a smooth scheme has enough sections to reach a dense set of special-fibre points (Bosch–Lütkebohmert–Raynaud, Néron Models, 2.3). It is used in the Néron model infrastructure, in [`NeronModelInfra.exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth`](thm.html#NeronModelInfra.exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] :
    Dense {x : {x : T // t.base x = IsLocalRing.closedPoint R} |
      ∃ s : Spec (CommRingCat.of R) ⟶ T, s ≫ t = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x.1} := by sorry
