-- Prove2me | Theorems.Thm_AlgebraicGeometry_genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/63c2d522-21a4-53f0-8390-ff05dd99b0d0
-- title:
--   Injective on points implies birational for smooth curves
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero, and let $gY : Y \to \operatorname{Spec} K$ and $gX : X \to \operatorname{Spec} K$ be morphisms of schemes with $Y$ and $X$ integral, both morphisms separated, and both smooth of relative dimension $1$. Let $h : Y \to X$ be a morphism over $K$, i.e. $h$ followed by $gX$ equals $gY$. Assume the following injectivity on geometric points: for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} K$, any two pairs $P, P'$ consisting of a morphism $\operatorname{Spec} k \to Y$ whose composite with $gY$ is $s$ have $P = P'$ as soon as the two underlying morphisms become equal after composing with $h$. The conclusion is twofold: the map on underlying topological spaces sends the generic point of $Y$ to the generic point of $X$, and the induced map of local rings $\mathcal{O}_{X,\,h(\eta_Y)} \to \mathcal{O}_{Y,\,\eta_Y}$ at the generic point of $Y$ is an isomorphism. Thus $h$ is dominant and induces an isomorphism of function fields.
--
--   This is the statement that a morphism of smooth separated integral curves over an algebraically closed field of characteristic zero which is injective on $k$-valued points (for all algebraically closed $k$ over the base) is birational. It is used in the comparison of Čerednik–Drinfeld quaternionic moduli schemes with pullbacks of coarse moduli spaces, where a candidate morphism is first shown to be injective on points and must then be upgraded to an isomorphism of function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra

theorem AlgebraicGeometry.genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {Y X : Scheme.{0}} (gY : Y ⟶ Spec (CommRingCat.of K)) (gX : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsIntegral X] [IsSeparated gY] [IsSeparated gX]
    (hY : SmoothOfRelativeDimension 1 gY) (hX : SmoothOfRelativeDimension 1 gX)
    (h : Y ⟶ X) (hh : h ≫ gX = gY)
    (hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
      (P P' : SchemeHomOver s gY), P.1 ≫ h = P'.1 ≫ h → P = P') :
    h.base (genericPoint Y) = genericPoint X ∧ IsIso (h.stalkMap (genericPoint Y)) := by sorry
