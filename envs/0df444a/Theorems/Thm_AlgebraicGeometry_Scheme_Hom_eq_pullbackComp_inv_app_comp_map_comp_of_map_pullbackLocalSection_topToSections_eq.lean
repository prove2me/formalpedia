-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq
-- name    : AlgebraicGeometry.Scheme.Hom.eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/db23f276-78d0-5ed7-b1a3-2c58740482c2
-- title:
--   Chain rule for pull-back maps on top differentials
-- statement:
--   Let $A \to B \to C$ be commutative rings forming a scalar tower, and let $gZ : Z \to \operatorname{Spec} A$, $gY : Y \to \operatorname{Spec} B$, $gX : X \to \operatorname{Spec} C$ be schemes over them, together with $\psi : Y \to Z$ satisfying $\psi$ followed by $gZ$ equals $gY$ followed by $\operatorname{Spec}(A \to B)$, and $\varphi : X \to Y$ satisfying $\varphi$ followed by $gY$ equals $gX$ followed by $\operatorname{Spec}(B \to C)$; fix $d \in \mathbb{N}$. For a structure morphism $f$ to an affine base, $f.\mathtt{topDifferentials}\ d$ denotes the sheafification of the $d$-th exterior power of the presheaf of relative Kähler differentials of the induced constant-base algebra structure, and $f.\mathtt{topToSections}\ d\ U$ the canonical map from $\bigwedge^d_{\Gamma(X,U)}$ of that presheaf at $U$ to its sections over $U$. Given morphisms $\theta_\psi : \psi^{*}(gZ.\mathtt{topDifferentials}\ d) \to gY.\mathtt{topDifferentials}\ d$, $\theta_\varphi : \varphi^{*}(gY.\mathtt{topDifferentials}\ d) \to gX.\mathtt{topDifferentials}\ d$ and $\theta : (\varphi \psi)^{*}(gZ.\mathtt{topDifferentials}\ d) \to gX.\mathtt{topDifferentials}\ d$, each assumed to be computed on affine charts by the canonical map on top forms: for instance for $\theta_\psi$, for all affine opens $U \subseteq Z$, $W \subseteq Y$ with $W \le \psi^{-1}U$, equipping $\Gamma(Z,U)$ with its $A$-algebra structure, $\Gamma(Y,W)$ with its $B$-algebra structure and with the $\Gamma(Z,U)$-algebra structure given by $\psi.\mathtt{appLE}\ U\ W$, and for any $A$-algebra structure on $\Gamma(Y,W)$ compatible with both towers, the restriction to $W$ of $\theta_\psi$ applied to the pull-back along $\psi$ of the local section $gZ.\mathtt{topToSections}\ d\ U\ \eta$ equals $gY.\mathtt{topToSections}\ d\ W$ of $\mathtt{topFormMap}\ A\ B\ \Gamma(Z,U)\ \Gamma(Y,W)\ d\ \eta$, for all $\eta \in \bigwedge^d_{\Gamma(Z,U)}$ of the Kähler presheaf at $U$ (similarly for $\theta_\varphi$ over $B \to C$ and for $\theta$ over $A \to C$ along $\varphi \psi$). Then $\theta$ equals the inverse of the component of `Scheme.Modules.pullbackComp φ ψ` at $gZ.\mathtt{topDifferentials}\ d$, followed by $\varphi^{*}\theta_\psi$, followed by $\theta_\varphi$.
--
--   This is the chain rule, or cocycle condition, for the morphisms on sheaves of top relative differential forms attached to a composite of morphisms of schemes over a tower of affine bases: a morphism characterised by the chart formula in terms of the functoriality map `topFormMap` on top exterior powers of Kähler differentials factors as the composite of the corresponding morphisms for the two factors. It is used in the construction of frames for top differentials in the treatment of the relative group law on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq.lean

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

theorem AlgebraicGeometry.Scheme.Hom.eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    {X Y Z : Scheme.{u}} (gZ : Z ⟶ Spec (CommRingCat.of A)) (gY : Y ⟶ Spec (CommRingCat.of B))
    (gX : X ⟶ Spec (CommRingCat.of C))
    (ψ : Y ⟶ Z) (hψ : ψ ≫ gZ = gY ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (d : ℕ)
    (θψ : (Scheme.Modules.pullback ψ).obj (gZ.topDifferentials d) ⟶ gY.topDifferentials d)
    (hθψ : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : IsAffineOpen W) (hWU : W ≤ ψ ⁻¹ᵁ U),
        letI := gZ.sectionsAlgebra U; letI := gY.sectionsAlgebra W
        letI : Algebra Γ(Z, U) Γ(Y, W) := (ψ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(Y, W)] [IsScalarTower A B Γ(Y, W)] [IsScalarTower A Γ(Z, U) Γ(Y, W)]
          (η : ⋀[Γ(Z, U)]^d (gZ.kaehlerPresheaf.obj (op U))),
          (gY.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θψ.app (ψ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection ψ (gZ.topToSections d U η))) =
            gY.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Z, U) Γ(Y, W) d η))
    (θφ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθφ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra B Γ(X, W)] [IsScalarTower B C Γ(X, W)] [IsScalarTower B Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θφ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap B C Γ(Y, U) Γ(X, W) d η))
    (θ : (Scheme.Modules.pullback (φ ≫ ψ)).obj (gZ.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ (φ ≫ ψ) ⁻¹ᵁ U),
        letI := gZ.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Z, U) Γ(X, W) := ((φ ≫ ψ).appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A C Γ(X, W)] [IsScalarTower A Γ(Z, U) Γ(X, W)]
          (η : ⋀[Γ(Z, U)]^d (gZ.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app ((φ ≫ ψ) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) (gZ.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A C Γ(Z, U) Γ(X, W) d η)) :
    θ = ((Scheme.Modules.pullbackComp φ ψ).app (gZ.topDifferentials d)).inv ≫
      (Scheme.Modules.pullback φ).map θψ ≫ θφ := by sorry
