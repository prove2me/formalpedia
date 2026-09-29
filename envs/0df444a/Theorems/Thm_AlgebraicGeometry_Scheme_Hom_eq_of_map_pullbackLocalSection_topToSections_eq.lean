-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq
-- name    : AlgebraicGeometry.Scheme.Hom.eq_of_map_pullbackLocalSection_topToSections_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/3b797326-9383-526f-b61c-cfd6f81a32ec
-- title:
--   Uniqueness of pullback maps on top differentials via affine charts
-- statement:
--   Let $A \to B$ be a homomorphism of commutative rings (given as an $A$-algebra structure on $B$), let $X, Y$ be schemes, and let $g_Y : Y \to \operatorname{Spec} A$, $g_X : X \to \operatorname{Spec} B$ and $\varphi : X \to Y$ be morphisms with $\varphi$ followed by $g_Y$ equal to $g_X$ followed by $\operatorname{Spec}$ of $A \to B$. Fix $d \in \mathbb{N}$ and write $\omega^d_{Y/A} =$ `gY.topDifferentials d`, the image under `Scheme.Modules.det d` of the sheafification of the presheaf of relative differentials of the constant $A$-structure map on $\mathcal{O}_Y$, and similarly $\omega^d_{X/B}$. Let $\theta, \theta'$ be two morphisms of $\mathcal{O}_X$-modules $\varphi^{*}\omega^d_{Y/A} \to \omega^d_{X/B}$. Assume of each of $\theta$ and $\theta'$ the following: for all affine opens $U \subseteq Y$ and $W \subseteq X$ with $W \le \varphi^{-1}U$, equipping $\Gamma(Y,U)$ with its $A$-algebra structure and $\Gamma(X,W)$ with its $B$-algebra structure coming from `sectionsAlgebra`, and with the $\Gamma(Y,U)$-algebra structure given by $\varphi$'s restriction map $\Gamma(Y,U) \to \Gamma(X,W)$, then for every $A$-algebra structure on $\Gamma(X,W)$ making both $A \to B \to \Gamma(X,W)$ and $A \to \Gamma(Y,U) \to \Gamma(X,W)$ scalar towers, and every $\eta \in \bigwedge^d_{\Gamma(Y,U)} \Omega_{\Gamma(Y,U)/A}$, the restriction to $W$ of the value of $\theta$ (respectively $\theta'$) at $\varphi^{-1}U$ on the canonical pullback section of `topToSections d U η` equals `topToSections d W` applied to $\mathrm{topFormMap}$ of $\eta$, the induced map $\bigwedge^d_{\Gamma(Y,U)} \Omega_{\Gamma(Y,U)/A} \to \bigwedge^d_{\Gamma(X,W)} \Omega_{\Gamma(X,W)/B}$. The conclusion is $\theta = \theta'$.
--
--   This is the uniqueness half of the construction of the pullback map on top relative differential forms: a morphism $\varphi^{*}\omega^d_{Y/A} \to \omega^d_{X/B}$ is pinned down by the requirement that on affine charts it be given by functoriality of Kähler differentials. It is used to identify such a map along composites and restrictions, and in the construction of frames for top differentials in the relative group law on Jacobians of good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq.lean

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

theorem AlgebraicGeometry.Scheme.Hom.eq_of_map_pullbackLocalSection_topToSections_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)
    (θ θ' : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η))
    (hθ' : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ'.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η)) :
    θ = θ' := by sorry
