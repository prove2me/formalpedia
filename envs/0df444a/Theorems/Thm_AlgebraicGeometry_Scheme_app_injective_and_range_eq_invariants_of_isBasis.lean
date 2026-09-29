-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis
-- name    : AlgebraicGeometry.Scheme.app_injective_and_range_eq_invariants_of_isBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/83619b0c-7ca7-5b3b-8a5a-d39b07a92bec
-- title:
--   Sections as invariants: from a basis to all opens
-- statement:
--   Let $\pi : M \to X$ be a morphism of schemes (in the lowest universe), let $H$ be a group and let $\rho : H \to \operatorname{Aut} M$ be a group homomorphism into the automorphism group of $M$ in the category of schemes, such that each automorphism $\rho(h)$ followed by $\pi$ equals $\pi$. For an open $V \subseteq X$ write $\pi^{*}_V$ for `π.app V`, the ring map $\Gamma(X,V) \to \Gamma(M, \pi^{-1}V)$ induced by $\pi$, and, for $h \in H$, write $\rho(h)^{*}_V$ for the map $\Gamma(M,\pi^{-1}V) \to \Gamma(M,\pi^{-1}V)$ obtained from $\rho(h)$ via `appLE`, using that $\rho(h)^{-1}(\pi^{-1}V) = \pi^{-1}V$ because $\rho(h)$ followed by $\pi$ is $\pi$. Assume $B$ is a set of opens of $X$ which is a basis of the topology, and that for every $W \in B$ the map $\pi^{*}_W$ is injective and its range is exactly the set of $s \in \Gamma(M,\pi^{-1}W)$ with $\rho(h)^{*}_W s = s$ for all $h \in H$. The conclusion is the conjunction of the same two assertions for every open $V \subseteq X$: $\pi^{*}_V$ is injective, and its range is the set of $s \in \Gamma(M,\pi^{-1}V)$ fixed by $\rho(h)^{*}_V$ for all $h \in H$. No finiteness is assumed of $H$.
--
--   This is the locality step in the identification of the structure sheaf of a quotient with the sheaf of invariants: the description of $\mathcal{O}_X(V)$ as $\mathcal{O}_M(\pi^{-1}V)^H$ need only be checked on a basis of opens. It is used in [`AlgebraicGeometry.Scheme.quotientInvariants_pullback_of_flat`](thm.html#AlgebraicGeometry.Scheme.quotientInvariants_pullback_of_flat), where the description is known on the basic opens of affine charts and is transported to arbitrary opens after a flat base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.app_injective_and_range_eq_invariants_of_isBasis
    {M X : Scheme.{0}} (π : M ⟶ X)
    {H : Type} [Group H] (ρ : H →* Aut M) (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
    (B : Set X.Opens) (hB : TopologicalSpace.Opens.IsBasis B)
    (hsecB : ∀ W ∈ B, Function.Injective (π.app W))
    (hinvB : ∀ W ∈ B, Set.range (π.app W) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ W) (π ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) :
    (∀ V : X.Opens, Function.Injective (π.app V)) ∧
    (∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) := by sorry
