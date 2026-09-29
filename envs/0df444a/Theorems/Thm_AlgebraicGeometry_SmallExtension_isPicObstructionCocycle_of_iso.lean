-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_of_iso
-- name    : AlgebraicGeometry.SmallExtension.isPicObstructionCocycle_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/f78313fe-db48-5161-b6fb-3cad4a7930f9
-- title:
--   Picard obstruction cocycles are insensitive to isomorphism
-- statement:
--   Let $B_1$ be a commutative ring and $k$ a field, let $V$ be an abelian group equipped with a $k$-module and a $B_1$-module structure, and let $\iota : V \to B_1$ be $B_1$-linear. Let $f : X \to \operatorname{Spec} B_1$ be a morphism of schemes, $g : X_0 \to X$ and $i : X_k \to X$ affine morphisms, $f_k : X_k \to \operatorname{Spec} k$ a morphism, and $\mathcal{U}$ an ordered affine cover of $X$ (a finite linearly ordered family of affine opens with supremum $\top$). Let $\mathcal{L}_0, \mathcal{M}_0$ be sheaves of modules on $X_0$ with an isomorphism $e : \mathcal{L}_0 \cong \mathcal{M}_0$, and let $c$ be a $k$-linear map from $\operatorname{Hom}_k(V,k)$ to the $2$-cochains, for the cover $i^{-1}\mathcal{U}$, of the presheaf of modules $U \mapsto \Gamma(X_k, U)$ over $f_k$; i.e. $c(\xi)$ assigns to each strictly increasing triple $r$ of indices a section of $\mathcal{O}_{X_k}$ on $\bigcap_j i^{-1}\mathcal{U}_{r_j}$. Assume `IsPicObstructionCocycle` holds for $\mathcal{L}_0$ and $c$: there are a Čech trivialisation $\tau$ of $\mathcal{L}_0$ over $g^{-1}\mathcal{U}$ (isomorphisms of the restriction of $\mathcal{L}_0$ to each $g^{-1}\mathcal{U}_a$ with the unit module) and families $u, u'$ of sections of $\mathcal{O}_X$ over the double intersections $\mathcal{U}_s$ such that $g^{\sharp}(u_s)$ restricts to the transition section of $\tau$ at $s$, $u_s u'_s = 1$, and for every triple $r$ the section $u_{\partial_2 r} u_{\partial_0 r} u'_{\partial_1 r} - 1$ on $\mathcal{U}_r$ admits a fibre reading by the $r$-component of $c$: there are $v_1,\dots,v_n \in V$ and sections $s_1,\dots,s_n$ of $\mathcal{O}_X$ on $\mathcal{U}_r$ with $\sum_j \iota(v_j) s_j$ equal to that section and $c(\xi)_r = \sum_j \xi(v_j)\,i^{\sharp}(s_j)$ after restriction. Then the same $c$ satisfies `IsPicObstructionCocycle` for $\mathcal{M}_0$.
--
--   This records that the Čech-theoretic obstruction data measuring the failure of a module on $X_0$ to descend, read off on the fibre $X_k$ through $\iota$, depends on the module only up to isomorphism; the sections $u, u'$ and the fibre readings are unchanged. It is used in the study of fake elliptic curves in the Čerednik–Drinfeld setting, where the Mumford bundle is compared with its Rosati translate through an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_of_iso.lean

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

theorem AlgebraicGeometry.SmallExtension.isPicObstructionCocycle_of_iso
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (𝒰 : X.OrderedAffineCover)
    (𝓛₀ 𝓜₀ : X₀.Modules) (e : 𝓛₀ ≅ 𝓜₀) (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c) :
    IsPicObstructionCocycle V ι f fk i g 𝒰 𝓜₀ c := by sorry
