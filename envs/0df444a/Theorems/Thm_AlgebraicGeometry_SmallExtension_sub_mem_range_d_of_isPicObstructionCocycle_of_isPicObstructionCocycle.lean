-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicObstructionCocycle_of_isPicObstructionCocycle
-- name    : AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicObstructionCocycle_of_isPicObstructionCocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ee9e63ab-4037-5cdd-8ec5-8fbd22b26531
-- title:
--   Picard obstruction cocycle well defined modulo coboundaries
-- statement:
--   Let $B_1$ be a local commutative ring, $B_0$ a commutative ring and $\pi : B_1 \to B_0$ a surjective ring homomorphism whose kernel $J = \ker\pi$ satisfies $J\cdot\mathfrak m_{B_1} = 0$ and $J \subseteq \mathfrak m_{B_1}$. Let $V$ be a finite-dimensional vector space over $k = \mathrm{ResidueField}\,B_1$, carrying a compatible $B_1$-module structure, and let $\iota : V \to B_1$ be an injective $B_1$-linear map whose image is $J$. Let $f : X \to \operatorname{Spec} B_1$ be separated and flat, let $g : X_0 \to X$ be affine with $(g, f_0, f, \operatorname{Spec}\pi)$ cartesian, and let $i : X_k \to X$ be affine with $(i, f_k, f, \operatorname{Spec}(\mathrm{residue}))$ cartesian. Let $\mathcal U$ be an ordered affine cover of $X$ (a finite linearly ordered family of affine opens with supremum $\top$), $\mathcal L_0$ a module on $X_0$, and let $c, c'$ be $k$-linear maps from $V^\vee$ to the Čech $2$-cochains of the structure presheaf $\mathcal O_{X_k}$ on the pulled-back cover $i^{-1}\mathcal U$, i.e. families of sections over the triple intersections. Assume both satisfy `IsPicObstructionCocycle`: for each there exist a Čech trivialisation $\tau$ of $\mathcal L_0$ on $g^{-1}\mathcal U$ (isomorphisms of its restriction to each chart with the unit module), and sections $u_s, u'_s \in \Gamma(X, \mathcal U_s)$ for every edge $s$, such that the pullback of $u_s$ along $g$, restricted to $g^{-1}\mathcal U_s$, is the transition section $\tau_s$, such that $u_s u'_s = 1$, and such that for every triple $r$ the section $u_{\partial_2 r} u_{\partial_0 r} u'_{\partial_1 r} - 1$ (restrictions to $\mathcal U_r$ understood) is fibre-read by the $r$-component of $c$, respectively $c'$: there are finitely many $v_j \in V$ and $s_j \in \Gamma(X, \mathcal U_r)$ with $\sum_j \iota(v_j)\, s_j$ equal to that section and, for every $\xi \in V^\vee$, the $r$-component of $c(\xi)$ equal to $\sum_j \xi(v_j)$ times the restriction to $i^{-1}\mathcal U_r$ of the $i$-pullback of $s_j$. The conclusion is that for every $\xi \in V^\vee$ the difference $c(\xi) - c'(\xi)$ lies in the image of the Čech differential $d : \check C^1(i^{-1}\mathcal U, \mathcal O_{X_k}) \to \check C^2(i^{-1}\mathcal U, \mathcal O_{X_k})$.
--
--   This is the well-definedness half of the deformation-theoretic obstruction to lifting a line bundle along a small extension: the Čech class of a Picard obstruction cocycle in $\check H^2(X_k, \mathcal O_{X_k})$, as a function of $\xi \in V^\vee$, depends only on $\mathcal L_0$ and the chosen cover, not on the trivialisation, the chosen lifts of transition sections or the chosen fibre readings. It is used in the construction of the Mumford bundle on fake elliptic curves in the Čerednik–Drinfeld setting, where vanishing of the obstruction produces the required lift.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_sub_mem_range_d_of_isPicObstructionCocycle_of_isPicObstructionCocycle.lean

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

theorem AlgebraicGeometry.SmallExtension.sub_mem_range_d_of_isPicObstructionCocycle_of_isPicObstructionCocycle
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
    (c c' : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c) (hc' : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c') :
    ∀ ξ : Module.Dual (ResidueField B₁) V,
      c ξ - c' ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 1) := by sorry
