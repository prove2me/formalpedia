-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_of_cechTrivialisation
-- name    : AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_of_cechTrivialisation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/2984a8e2-2f44-5fad-ae61-aa4988657e22
-- title:
--   Existence of a closed Picard obstruction cocycle
-- statement:
--   Let $B_1$ be a commutative local ring, $\pi \colon B_1 \to B_0$ a surjective ring homomorphism whose kernel satisfies $\ker\pi \cdot \mathfrak m_{B_1} = 0$ and $\ker\pi \subseteq \mathfrak m_{B_1}$, and let $V$ be a finite-dimensional vector space over the residue field of $B_1$, equipped with a compatible $B_1$-module structure, together with an injective $B_1$-linear map $\iota \colon V \to B_1$ whose image is exactly $\ker\pi$ viewed as a $B_1$-submodule. Let $f \colon X \to \operatorname{Spec} B_1$ be separated and flat, let $g \colon X_0 \to X$ be affine and fit into a cartesian square over $\operatorname{Spec}\pi$ with $f_0 \colon X_0 \to \operatorname{Spec} B_0$, and let $i \colon X_k \to X$ be affine and fit into a cartesian square over the residue map with $f_k \colon X_k \to \operatorname{Spec} k$, $k$ the residue field. Let $\mathcal U$ be a finite linearly ordered cover of $X$ by affine opens, let $\mathcal L_0$ be an $\mathcal O_{X_0}$-module, and let $\tau$ be a Čech trivialisation of $\mathcal L_0$ on the preimage cover $g^{-1}\mathcal U$, i.e. isomorphisms of the pullback of $\mathcal L_0$ to each $g^{-1}U_a$ with the unit module. Then there is a $k$-linear map $c$ from the dual $V^\vee$ to the $2$-cochains of the presheaf of sections of $\mathcal O_{X_k}$ on $i^{-1}\mathcal U$ such that `IsPicObstructionCocycle` holds for $c$ and each $c(\xi)$ is annihilated by the Čech differential in degree $2$. Unfolded, the first clause says: there are a Čech trivialisation $\tau'$ of $\mathcal L_0$ on $g^{-1}\mathcal U$ (the given $\tau$ shows such exist), and sections $u_s, u'_s \in \Gamma(X, U_s)$ over the intersections indexed by strictly increasing pairs $s$, with the image of $u_s$ in $\Gamma(X_0, g^{-1}U_s)$ equal to the transition section of $\tau'$ at $s$, with $u_s u'_s = 1$, and such that for every strictly increasing triple $r$ the section $u_{\partial_2 r} u_{\partial_0 r} u'_{\partial_1 r} - 1$ on $U_r$ admits the fibre reading $\xi \mapsto c(\xi)_r$: there are finitely many $v_j \in V$ and $s_j \in \Gamma(X, U_r)$ with $\sum_j \iota(v_j) s_j$ equal to that section and $c(\xi)_r = \sum_j \xi(v_j) \cdot (s_j|_{X_k})$ restricted to the corresponding intersection in $i^{-1}\mathcal U$.
--
--   This is the existence half of the Čech obstruction theory for lifting a line bundle along a small (square-zero) extension of local rings, expressed in terms of transition functions: the obstruction is produced as a closed $2$-cochain with values in $\mathcal O_{X_k}$, linear in $V^\vee$. It is used in the construction of invertible modules on deformations of fake elliptic curves, where it supplies the obstruction class whose vanishing is then analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_of_cechTrivialisation.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_of_cechTrivialisation
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
    (𝓛₀ : X₀.Modules) (τ : Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) :
    ∃ c : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2,
      IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c ∧
      ∀ ξ : Module.Dual (ResidueField B₁) V, (OModulePresheaf.unit fk).d (𝒰.comap i) 2 (c ξ) = 0 := by sorry
