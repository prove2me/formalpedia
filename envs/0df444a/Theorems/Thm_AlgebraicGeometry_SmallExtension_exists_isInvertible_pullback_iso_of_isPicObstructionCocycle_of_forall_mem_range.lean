-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range
-- name    : AlgebraicGeometry.SmallExtension.exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/7a4ed72c-b7e9-5b2f-9e7d-c4917e036d94
-- title:
--   Lifting a module along a small extension when the Picard obstruction is a coboundary
-- statement:
--   Let $B_1$ be a local commutative ring, $B_0$ a commutative ring and $\pi \colon B_1 \to B_0$ a surjective ring homomorphism whose kernel satisfies $\ker\pi \cdot \mathfrak m_{B_1} = 0$ and $\ker \pi \subseteq \mathfrak m_{B_1}$. Let $V$ be a finite-dimensional vector space over the residue field $k = \mathrm{ResidueField}\,B_1$, equipped with a compatible $B_1$-module structure, and let $\iota \colon V \to B_1$ be an injective $B_1$-linear map whose image is $\ker\pi$. Let $f \colon X \to \operatorname{Spec} B_1$ be separated and flat, let $g \colon X_0 \to X$ and $i \colon X_k \to X$ be affine morphisms fitting into pullback squares exhibiting $X_0$ over $\operatorname{Spec} B_0$ and $X_k$ over $\operatorname{Spec} k$ as the base changes of $f$ along $\operatorname{Spec}\pi$ and along $\operatorname{Spec}$ of the residue map, let $\mathcal U$ be a finite linearly ordered affine open cover of $X$, and let $\mathcal L_0$ be a module on $X_0$. Let $c \colon V^\vee \to \check C^2(i^{-1}\mathcal U; \mathcal O_{X_k})$ be $k$-linear, where the target consists of families of sections of $\mathcal O_{X_k}$ over the intersections indexed by $2$-simplices of the pulled-back cover. Assume the predicate `IsPicObstructionCocycle` holds for $c$: there are a Čech trivialisation $\tau$ of $\mathcal L_0$ over $g^{-1}\mathcal U$ and families $u, u'$ of sections of $\mathcal O_X$ over the pairwise intersections $\mathcal U_s$ ($s$ a $1$-simplex) such that the image of $u_s$ under $g$ followed by restriction is the transition section $\tau_s$, such that $u_s u'_s = 1$, and such that for every $2$-simplex $r$ the section $u_{r_2} u_{r_0} u'_{r_1} - 1$ on $\mathcal U_r$ is a fibre reading of the component $c(\cdot)_r$, i.e. there are finitely many $v_j \in V$ and sections $s_j$ on $\mathcal U_r$ with $\sum_j \iota(v_j) s_j$ equal to that section and $c(\xi)_r = \sum_j \xi(v_j)\, i^{\sharp}(s_j)$ for all $\xi \in V^\vee$. Assume further that $c(\xi)$ lies in the image of the Čech differential $\check C^1 \to \check C^2$ for every $\xi \in V^\vee$. Then there exists a module $\mathcal L$ on $X$ which is invertible, in the sense that every point of $X$ has an open neighbourhood $U$ with the restriction of $\mathcal L$ to $U$ isomorphic to the unit module on $U$, together with an isomorphism $g^{*}\mathcal L \cong \mathcal L_0$.
--
--   This is the lifting half of the Čech obstruction theory for invertible modules along a small extension: vanishing of the obstruction class, here in the explicit form that each coordinate of the obstruction cocycle is a coboundary, suffices for the invertible module on the special fibre $X_0$ to be lifted to $X$. It is used in the construction of line bundles on fake elliptic curves over small extensions of local rings, in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range
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
    (𝓛₀ : X₀.Modules)
    (c : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c)
    (hcob : ∀ ξ : Module.Dual (ResidueField B₁) V,
      c ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 1)) :
    ∃ 𝓛 : X.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) := by sorry
