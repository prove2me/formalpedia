-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
-- name    : AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/71e6c674-7a18-5496-9eef-8d3c4d61e894
-- title:
--   Two Picard deformation cocycles differ by a Čech coboundary
-- statement:
--   Let $\pi \colon B_1 \to B_0$ be a surjective homomorphism of commutative rings with $B_1$ local, such that $\ker\pi \cdot \mathfrak m_{B_1} = 0$ and $\ker\pi \subseteq \mathfrak m_{B_1}$. Let $V$ be a finite-dimensional vector space over the residue field $k = \operatorname{ResidueField} B_1$, equipped with a compatible $B_1$-module structure, and let $\iota \colon V \to B_1$ be an injective $B_1$-linear map whose image is exactly $\ker\pi$. Let $f \colon X \to \operatorname{Spec} B_1$ be separated and flat, let $g \colon X_0 \to X$ be an affine morphism making $(X_0, f_0)$ the base change of $f$ along $\operatorname{Spec}\pi$, and let $i \colon X_k \to X$ be an affine morphism making $(X_k, f_k)$ the base change of $f$ along the residue map. Let $\mathcal U$ be an ordered affine cover of $X$ (a finite linearly ordered family of affine opens covering $X$), let $M$ be a module on $X$ and let $\varphi_0$ be an isomorphism $g^*M \cong \mathcal O_{X_0}$. Let $w, w'$ be $k$-linear maps from $V^\vee$ to the $1$-cochains of the unit $\mathcal O$-module presheaf of $f_k$ on the pulled-back cover $i^{-1}\mathcal U$, each satisfying `IsPicDeformationCocycle`: there are a Čech trivialisation $\tau$ of $M$ on $\mathcal U$ (isomorphisms $M|_{\mathcal U_a} \cong \mathcal O_{\mathcal U_a}$), and sections $e_a, e'_a \in \Gamma(X, \mathcal U_a)$ with $e_a e'_a = 1$, such that $g^\#(e_a)$ is the unit section attached to the automorphism of $\mathcal O$ on $g^{-1}\mathcal U_a$ obtained by comparing $\tau$ pulled back along $g$ with $\varphi_0$, and such that for each $1$-simplex $s$ the section $\tau_s \cdot e'_{s_0}|\cdot e_{s_1}| - 1$ on $\mathcal U_s$ is read on the fibre by the $s$-component of $w$ (respectively $w'$), i.e. there are $v_j \in V$ and sections $t_j$ on $\mathcal U_s$ with $\sum_j \iota(v_j) t_j$ equal to that section and $w(\xi)_s = \sum_j \xi(v_j)\,(i^\# t_j)|$ for all $\xi$. The conclusion is pointwise: for every $\xi \in V^\vee$, the difference $w(\xi) - w'(\xi)$ lies in the image of the degree-$0$ Čech differential $d$ of the unit presheaf on $i^{-1}\mathcal U$.
--
--   This is the well-definedness statement for the Čech-cocycle description of the obstruction to deforming a line bundle, together with its trivialisation, across a small extension $B_1 \to B_0$: the class of the cocycle in $H^1(i^{-1}\mathcal U, \mathcal O_{X_k}) \otimes V$ does not depend on the choice of trivialisation and of lifts of the transition discrepancies. It feeds the construction of isomorphisms of line bundles on abelian schemes used in the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicDeformationCocycle_of_isPicDeformationCocycle
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w w' : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) (hw' : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w') :
    ∀ ξ : Module.Dual (ResidueField B₁) V,
      w ξ - w' ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 0) := by sorry
