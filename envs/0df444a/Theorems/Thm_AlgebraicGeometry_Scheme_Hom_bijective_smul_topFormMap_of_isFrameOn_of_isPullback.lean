-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_bijective_smul_topFormMap_of_isFrameOn_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Hom.bijective_smul_topFormMap_of_isFrameOn_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/52a88577-9ade-53a6-99ad-7207bb1469aa
-- title:
--   Pulled-back frame of top differentials freely generates on charts
-- statement:
--   Let $A \to B$ be a homomorphism of commutative rings, let $gY \colon Y \to \operatorname{Spec} A$ and $gX \colon X \to \operatorname{Spec} B$ be morphisms of schemes, and let $\varphi \colon X \to Y$ be a morphism such that the square formed by $\varphi$, $gX$, $gY$ and $\operatorname{Spec}$ of $A \to B$ is cartesian ($\varphi$ followed by $gY$ equals $gX$ followed by $\operatorname{Spec}(A \to B)$, and the square is a pullback). Assume $gY$ is smooth of relative dimension $d$. Let $U \subseteq Y$ be an affine open and $s$ a section over $U$ of `gY.topDifferentials d`, the $d$-th determinant (exterior power, sheafified) of the relative Kähler module of $gY$, and assume `IsFrameOn s U`: for every open $W \le U$ the map $g \mapsto g \cdot (s|_W)$ from $\Gamma(X, W)$ — here $\Gamma(Y, W)$ — to the sections of that module over $W$ is bijective. Let $\eta \in \bigwedge^d_{\Gamma(Y,U)} \Omega_{\Gamma(Y,U)/A}$ be a chart expression for $s$, i.e. `gY.topToSections d U η = s`. Let $W \subseteq X$ be an affine open with $W \le \varphi^{-1}U$, equip $\Gamma(Y,U)$ with its $A$-algebra structure and $\Gamma(X,W)$ with its $B$-algebra structure coming from the structure morphisms and with the $\Gamma(Y,U)$-algebra structure given by $\varphi^{\sharp} =$ `φ.appLE U W hWU`, and assume an $A$-algebra structure on $\Gamma(X,W)$ compatible with both towers $A \to B \to \Gamma(X,W)$ and $A \to \Gamma(Y,U) \to \Gamma(X,W)$. Then the map $c \mapsto c \cdot \mathrm{topFormMap}(\eta)$ from $\Gamma(X,W)$ to $\bigwedge^d_{\Gamma(X,W)} \Omega_{\Gamma(X,W)/B}$ is bijective, where $\mathrm{topFormMap}$ is the $\Gamma(Y,U)$-linear base-change map on $d$-th exterior powers of differentials; that is, the pulled-back chart expression of $\eta$ is a free generator of $\bigwedge^d_{\Gamma(X,W)} \Omega_{\Gamma(X,W)/B}$.
--
--   This is the chart-level (sheaf-free) form of the statement that a frame of the sheaf of top relative differentials pulls back, along a cartesian square over $\operatorname{Spec} B \to \operatorname{Spec} A$, to a frame: on each affine chart the base-changed differential form is a basis of the free rank-one module of top differentials. It is used in the construction of invariant differentials for the relative group law on Jacobians with good reduction, where such a generator is needed simultaneously on all affine charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_bijective_smul_topFormMap_of_isFrameOn_of_isPullback.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.bijective_smul_topFormMap_of_isFrameOn_of_isPullback
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B)))) (d : ℕ)
    [SmoothOfRelativeDimension d gY]
    (U : Y.Opens) (hU : IsAffineOpen U) (s : Γ(gY.topDifferentials d, U)) (hs : Scheme.Modules.IsFrameOn s U)
    (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U)))
    (hη : gY.topToSections d U η = s)
    (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U) :
    letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
    letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
    ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)],
      Function.Bijective fun c : Γ(X, W) =>
        c • NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η := by sorry
