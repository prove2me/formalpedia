-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff
-- name    : AlgebraicGeometry.Scheme.germ_app_appIso_inv_mem_maximalIdeal_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7d742aee-c718-5eb9-8118-8e28391fbc77
-- title:
--   Germ of a chart function lies in the maximal ideal iff
-- statement:
--   Let $X$ and $Y$ be schemes, $f\colon Y \to X$ a morphism of schemes, $R$ a commutative ring and $\iota\colon \operatorname{Spec} R \to X$ an open immersion; let $y$ be a point of $Y$, $q$ a prime ideal of $R$, and assume that $f(y)$ lies in the open subset $\iota(\operatorname{Spec} R)$ of $X$ (the image of the top open under $\iota$) and that $\iota(q) = f(y)$; let $t \in R$. Consider the section of $\mathcal{O}_Y$ over $f^{-1}(\iota(\operatorname{Spec} R))$ obtained from $t$ in three steps: pass from $t$ to the corresponding global section of $\mathcal{O}_{\operatorname{Spec} R}$ via the inverse of the isomorphism $\Gamma(\operatorname{Spec} R, \top) \cong R$, transport it to a section over $\iota(\operatorname{Spec} R)$ by the inverse of the isomorphism $\iota.\mathrm{appIso}$ attached to the open immersion $\iota$, and pull it back along $f$. The assertion is that the germ of this section at $y$ lies in the maximal ideal of the local ring $\mathcal{O}_{Y,y}$ if and only if $t \in q$.
--
--   This is the standard reading of a function on an affine chart at a point of a scheme mapping into that chart: membership of the germ in the maximal ideal of the stalk is exactly membership of the function in the prime ideal corresponding to the chart point. It is used in the work on two-chart models of modular curves, by [`ModularCurve.DRModelPackageLevel.phi_algebraMap_stalk_mem_integers_comp_genericPoint`](thm.html#ModularCurve.DRModelPackageLevel.phi_algebraMap_stalk_mem_integers_comp_genericPoint) and [`ModularCurve.DRModelPackage.polynomialEval_mem_range_algebraMap_stalk_and_inv_mem_of_map_ne_zero`](thm.html#ModularCurve.DRModelPackage.polynomialEval_mem_range_algebraMap_stalk_and_inv_mem_of_map_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
universe u

theorem AlgebraicGeometry.Scheme.germ_app_appIso_inv_mem_maximalIdeal_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (R : CommRingCat.{u}) (ι : Spec R ⟶ X) [IsOpenImmersion ι]
    (y : ↥Y) (q : PrimeSpectrum ↑R) (hy : f.base y ∈ ι ''ᵁ ⊤) (hq : ι.base q = f.base y) (t : ↑R) :
    (Y.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) y hy).hom
        ((f.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv t))) ∈
      IsLocalRing.maximalIdeal ↑(Y.presheaf.stalk y) ↔ t ∈ q.asIdeal := by sorry
