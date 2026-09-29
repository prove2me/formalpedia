-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/5dd739ad-a1c2-5803-943c-7fd82960d323
-- title:
--   Birational K-morphism of smooth curves, injective on points, is an open immersion
-- statement:
--   Let $K$ be an algebraically closed field and let $gY : Y \to \operatorname{Spec} K$ and $gX : X \to \operatorname{Spec} K$ be morphisms of schemes (in the zeroth universe) with $Y$ and $X$ integral, both morphisms separated, and both smooth of relative dimension $1$ in the sense of Mathlib's `SmoothOfRelativeDimension 1`. Let $h : Y \to X$ be a morphism over $K$, that is, $h$ followed by $gX$ equals $gY$, and assume: the underlying continuous map of $h$ sends the generic point of $Y$ to the generic point of $X$; the induced map of stalks $\mathcal{O}_{X, h(\eta_Y)} \to \mathcal{O}_{Y,\eta_Y}$ at the generic point is an isomorphism; and $h$ is injective on geometric points over $K$ in the following sense: for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} K$, any two morphisms $P, P' : \operatorname{Spec} k \to Y$ satisfying $P \circ{}\!\!\!\!\phantom{.} gY = s$ and $P' \circ{}\!\!\!\!\phantom{.} gY = s$ (each $\operatorname{Spec} k \to Y$ taken together with its compatibility with $gY$ and $s$) and such that $P$ followed by $h$ equals $P'$ followed by $h$ are equal. The conclusion is that $h$ is an open immersion.
--
--   This is the curve case of Zariski's main theorem in the form used to recognise a birational morphism of smooth separated integral curves over an algebraically closed field as an open immersion, once it is known to be injective on geometric points. It is used in the Čerednik–Drinfeld part of the development, where comparisons of coarse moduli schemes for quaternionic data are promoted from bijectivity statements on points to isomorphisms onto open subschemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra

theorem AlgebraicGeometry.isOpenImmersion_of_isIso_stalkMap_genericPoint_of_injective_points_of_smoothOfRelativeDimension_one
    {K : Type} [Field K] [IsAlgClosed K]
    {Y X : Scheme.{0}} (gY : Y ⟶ Spec (CommRingCat.of K)) (gX : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsIntegral X] [IsSeparated gY] [IsSeparated gX]
    (hY : SmoothOfRelativeDimension 1 gY) (hX : SmoothOfRelativeDimension 1 gX)
    (h : Y ⟶ X) (hh : h ≫ gX = gY)
    (hgen : h.base (genericPoint Y) = genericPoint X) (hbir : IsIso (h.stalkMap (genericPoint Y)))
    (hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
      (P P' : SchemeHomOver s gY), P.1 ≫ h = P'.1 ≫ h → P = P') :
    IsOpenImmersion h := by sorry
