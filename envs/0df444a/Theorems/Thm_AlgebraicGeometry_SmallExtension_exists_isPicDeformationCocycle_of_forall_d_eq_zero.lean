-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_forall_d_eq_zero
-- name    : AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_forall_d_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/410a9492-fa37-59a7-832c-e7f3b2cb9cbd
-- title:
--   Realising closed cocycles as Picard deformation data
-- statement:
--   Let $\pi\colon B_1\to B_0$ be a surjective ring homomorphism with $B_1$ local, satisfying $\ker\pi\cdot\mathfrak m_{B_1}=0$ and $\ker\pi\subseteq\mathfrak m_{B_1}$. Let $V$ be a finite-dimensional vector space over $k=\mathrm{ResidueField}\,B_1$, carrying a compatible $B_1$-module structure, and let $\iota\colon V\to B_1$ be an injective $B_1$-linear map whose image is $\ker\pi$. Let $f\colon X\to\operatorname{Spec}B_1$ be separated and flat, let $g\colon X_0\to X$ be affine with $(g,f_0,f,\operatorname{Spec}\pi)$ a pullback square over $f_0\colon X_0\to\operatorname{Spec}B_0$, and let $i\colon X_k\to X$ be affine with $(i,f_k,f,\operatorname{Spec}(\mathrm{residue}))$ a pullback square over $f_k\colon X_k\to\operatorname{Spec}k$. Let $\mathcal U$ be an ordered affine cover of $X$ (a finite linearly ordered family of affine opens with supremum $\top$), and let $w\colon V^\vee\to\check C^1$ be $k$-linear into the $1$-cochains of the presheaf of modules $\mathcal O$ on the cover $i^{-1}\mathcal U$, i.e. families of sections over the intersections $\bigcap_j(i^{-1}\mathcal U)(s_j)$, with $d\,w(\xi)=0$ for every $\xi$. Then there are a module $N$ on $X$ and an isomorphism $\varphi_0\colon g^*N\cong\mathcal O_{X_0}$ such that $N$ is invertible (every point has an open neighbourhood $U$ with $N|_U\cong\mathcal O_U$) and $(N,\varphi_0)$ is a Picard deformation cocycle for $w$: there exist a Čech trivialisation $\tau$ of $N$ over $\mathcal U$ and sections $e_a,e'_a\in\Gamma(X,\mathcal U_a)$ with $e_ae'_a=1$, such that $g^\#(e_a)$ is the unit automorphism section comparing $\tau$ pulled back along $g$ with $\varphi_0$, and for every $1$-simplex $s$ the section $\tau.\mathrm{transition}(s)\cdot e'_{s_0}|\cdot e_{s_1}|-1$ is a fibre reading of the $s$-component of $w$, meaning it can be written as $\sum_j\iota(v_j)\,t_j$ with $v_j\in V$, $t_j\in\Gamma(X,\mathcal U.\mathrm{inter}\,s)$ and $w(\xi)_s=\sum_j\xi(v_j)\,(i^\#t_j)|$ for all $\xi\in V^\vee$.
--
--   This is the surjectivity half of the identification of the kernel of $\operatorname{Pic}X\to\operatorname{Pic}X_0$ for a small extension with $\check H^1(X_k,\mathcal O)\otimes_k\ker\pi$: every closed Čech $1$-cocycle with values in $V^\vee$ is realised by an invertible module on the thickening together with a trivialisation of its restriction to $X_0$. It is used in the construction of isomorphisms $\mathcal L\otimes\mathcal L\cong\mathcal O$ for fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_forall_d_eq_zero.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_forall_d_eq_zero
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
    (w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : ∀ ξ : Module.Dual (ResidueField B₁) V, (OModulePresheaf.unit fk).d (𝒰.comap i) 1 (w ξ) = 0) :
    ∃ (N : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit X₀.ringCatSheaf),
      Scheme.Modules.IsInvertible N ∧ IsPicDeformationCocycle V ι f fk i g 𝒰 N φ₀ w := by sorry
