-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk
-- name    : AlgebraicGeometry.Scheme.exists_opens_extension_of_fromSpecStalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/61e721c9-f161-554a-951f-0a5a1b894e76
-- title:
--   Spreading out a morphism from Specmathcal O_{G,η} over a base
-- statement:
--   Let $S$, $G$, $H$ be schemes (in a fixed universe), and let $s_G\colon G\to S$ and $s_H\colon H\to S$ be morphisms with $s_H$ locally of finite type. Let $\eta$ be a point of $G$ satisfying Mathlib's germ-injectivity condition `G.IsGermInjectiveAt η`, which provides arbitrarily small affine open neighbourhoods of $\eta$ on which the restriction of sections to the stalk $\mathcal O_{G,\eta}$ is injective. Suppose given a morphism $w\colon\operatorname{Spec}\mathcal O_{G,\eta}\to H$ that is compatible with the base, in the sense that $w$ followed by $s_H$ equals `G.fromSpecStalk η` followed by $s_G$. The assertion is that there exist an open subscheme $U$ of $G$, a proof that $\eta\in U$, and a morphism $v\colon U\to H$ such that, first, $v$ followed by $s_H$ equals the open immersion `U.ι` followed by $s_G$ (so $v$ is a morphism over $S$), and, second, the canonical map `U.fromSpecStalkOfMem η hη` from $\operatorname{Spec}\mathcal O_{G,\eta}$ to $U$ followed by $v$ equals $w$ (so $v$ extends $w$).
--
--   This is the germ-injective form of the spreading-out principle for morphisms into a target locally of finite type over the base (EGA IV 8.13/8.14): a point-local $S$-morphism out of $\operatorname{Spec}$ of a local ring of $G$ already comes from an open neighbourhood of that point. It is used in the form [`AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph`](thm.html#AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph) and in the construction of charts near index-one points in the Néron model infrastructure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.exists_opens_extension_of_fromSpecStalk
    {S G H : Scheme.{u}} (sG : G ⟶ S) (sH : H ⟶ S) [LocallyOfFiniteType sH]
    (η : G) [G.IsGermInjectiveAt η]
    (w : Spec (G.presheaf.stalk η) ⟶ H) (hw : w ≫ sH = G.fromSpecStalk η ≫ sG) :
    ∃ (U : G.Opens) (hη : η ∈ U) (v : (U : Scheme.{u}) ⟶ H),
      v ≫ sH = U.ι ≫ sG ∧ U.fromSpecStalkOfMem η hη ≫ v = w := by sorry
