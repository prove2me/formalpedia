-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
-- name    : AlgebraicGeometry.Scheme.Hom.exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/966a6e63-202f-5390-a223-c95f9a19df47
-- title:
--   Pullback morphism on top differentials, computed on affine charts
-- statement:
--   Let $A$ be a commutative ring, $B$ an $A$-algebra, and let $X,Y$ be schemes equipped with morphisms $g_Y : Y \to \operatorname{Spec} A$ and $g_X : X \to \operatorname{Spec} B$, together with $\varphi : X \to Y$ such that $\varphi$ followed by $g_Y$ equals $g_X$ followed by $\operatorname{Spec}$ of the structure map $A \to B$; let $d \in \mathbb{N}$. Writing $\omega^d_{g} =$ `g.topDifferentials d` for the $d$-th sheafified exterior power (the functor `Scheme.Modules.det`) of the sheafified relative Kähler module of the structure morphism $g$, the assertion is that there exists a morphism of $\mathcal{O}_X$-modules $\theta : \varphi^{*}\omega^d_{g_Y} \to \omega^d_{g_X}$ with the following chart-level compatibility: for all opens $U \subseteq Y$ and $W \subseteq X$ with $U$ and $W$ affine and $W \le \varphi^{-1}U$, where $\Gamma(Y,U)$ is an $A$-algebra and $\Gamma(X,W)$ a $B$-algebra via the structure morphisms (`sectionsAlgebra`, i.e. the maps induced by $g_Y$, $g_X$ through the $\Gamma$–$\operatorname{Spec}$ isomorphism) and $\Gamma(X,W)$ is a $\Gamma(Y,U)$-algebra via $\varphi$'s `appLE` map, and for any $A$-algebra structure on $\Gamma(X,W)$ making both $A \to B \to \Gamma(X,W)$ and $A \to \Gamma(Y,U) \to \Gamma(X,W)$ scalar towers, every $\eta \in \bigwedge^d_{\Gamma(Y,U)} \Omega_{\Gamma(Y,U)/A}$ (the sections over $U$ of the presheaf of relative differentials of `constToPresheaf`) satisfies: the restriction to $W$ of $\theta$ applied, over $\varphi^{-1}U$, to the canonical pullback (`pullbackLocalSection`, the unit of the pullback–pushforward adjunction) of the section `topToSections` of $\eta$ over $U$ coincides with the section `topToSections` over $W$ of `topFormMap` $A\, B\, \Gamma(Y,U)\, \Gamma(X,W)\, d\, \eta \in \bigwedge^d_{\Gamma(X,W)} \Omega_{\Gamma(X,W)/B}$.
--
--   This is the existence of the pullback map on sheaves of top-degree relative differential forms along a morphism over a base change $A \to B$, pinned down by its effect on affine charts, where it is the exteriorised differentials map $\bigwedge^d \Omega_{\Gamma(Y,U)/A} \to \bigwedge^d \Omega_{\Gamma(X,W)/B}$. It is used in the study of frames for sheaves of top differentials — in the bijectivity criterion `bijective_smul_topFormMap_of_isFrameOn_of_isPullback` and in the construction of frames compatible with the relative group law on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ) :
    ∃ θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d,
      ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η) := by sorry
