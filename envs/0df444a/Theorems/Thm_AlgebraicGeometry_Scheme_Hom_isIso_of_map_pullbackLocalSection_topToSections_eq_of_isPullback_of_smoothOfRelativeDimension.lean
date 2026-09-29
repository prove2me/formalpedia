-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
-- name    : AlgebraicGeometry.Scheme.Hom.isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/9c8cd96f-f8c9-5317-9916-895725d79619
-- title:
--   Base change isomorphism for top relative differentials, smooth case
-- statement:
--   Let $A$ be a commutative ring and $B$ an $A$-algebra, let $gY : Y \to \operatorname{Spec} A$ and $gX : X \to \operatorname{Spec} B$ be morphisms of schemes and let $\varphi : X \to Y$ be such that the square formed by $\varphi$, $gX$, $gY$ and $\operatorname{Spec}$ of $A \to B$ is cartesian, so that $X$ is the base change of $Y$ along $A \to B$. Fix $d \in \mathbb{N}$ and assume $gY$ is smooth of relative dimension $d$ (no smoothness of $gX$ is assumed). Let $\theta$ be a morphism of $\mathcal{O}_X$-modules from the pullback along $\varphi$ of $gY.\mathrm{topDifferentials}\ d$ — the sheafified $d$-th exterior power of the sheafified relative differentials of $Y$ over the constant presheaf $A$ — to $gX.\mathrm{topDifferentials}\ d$. The hypothesis on $\theta$ is that for all affine opens $U \subseteq Y$ and $W \subseteq X$ with $W \le \varphi^{-1}U$, equipping $\Gamma(Y,U)$ and $\Gamma(X,W)$ with the algebra structures over $A$, over $B$ and over each other coming from $gY$, $gX$ and $\varphi.\mathrm{appLE}$, and for any compatible $A$-algebra structure on $\Gamma(X,W)$ (scalar towers $A$–$B$–$\Gamma(X,W)$ and $A$–$\Gamma(Y,U)$–$\Gamma(X,W)$), and for every $\eta \in \bigwedge^d_{\Gamma(Y,U)} \Omega[\Gamma(Y,U)/A]$: the restriction to $W$ of $\theta$ evaluated on $\varphi^{-1}U$ at the canonical pullback local section of $gY.\mathrm{topToSections}\ d\ U\ \eta$ equals $gX.\mathrm{topToSections}\ d\ W$ applied to the image of $\eta$ under [`NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d`](def/NeronModelInfra_TopFormOrder.html#L31), the functoriality map $\bigwedge^d_{\Gamma(Y,U)} \Omega[\Gamma(Y,U)/A] \to \bigwedge^d_{\Gamma(X,W)} \Omega[\Gamma(X,W)/B]$. The conclusion is that $\theta$ is an isomorphism of $\mathcal{O}_X$-modules.
--
--   This is the statement that the sheaf of top-degree relative differentials commutes with base change, in the form needed when the target of the square is smooth of relative dimension $d$: a morphism $\varphi^*\omega^d_{Y/A} \to \omega^d_{X/B}$ given on affine charts by functoriality of Kähler differentials is an isomorphism. It is used to transport frames and left-invariant top forms along cartesian squares, notably in the construction of the relative group law on the Jacobian with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension.lean

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

theorem AlgebraicGeometry.Scheme.Hom.isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B)))) (d : ℕ)
    [SmoothOfRelativeDimension d gY]
    (θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η)) :
    IsIso θ := by sorry
