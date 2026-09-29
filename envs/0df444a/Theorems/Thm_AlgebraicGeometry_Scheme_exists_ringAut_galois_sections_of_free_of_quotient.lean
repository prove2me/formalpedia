-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient
-- name    : AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/6fd4b8da-6483-546a-9b01-76869d99ef8b
-- title:
--   Affine Galois data for a free finite quotient of schemes
-- statement:
--   Let $X,Y$ be schemes, $G$ a finite group and $\rho : G \to \operatorname{Aut}(X)$ a group homomorphism, subject to the following hypotheses: every point of $X$ lies in an affine open $U$ with $(\rho g)^{-1}(U) = U$ for all $g$; a morphism $\pi : X \to Y$ satisfies $(\rho g)$ followed by $\pi$ equal to $\pi$ for all $g$, is an affine morphism, is surjective on points, and has fibres equal to $G$-orbits (for all $x,x'$, $\pi(x) = \pi(x')$ iff $(\rho g)(x) = x'$ for some $g$); for every open $V \subseteq Y$ the map $\pi^\sharp_V : \Gamma(Y,V) \to \Gamma(X,\pi^{-1}V)$ is injective with image exactly the elements fixed by all the restrictions of $(\rho g)^\sharp$ to $\pi^{-1}V$; and the action is free on field-valued points: for every field $K$, every morphism $x : \operatorname{Spec} K \to X$ and every $g$ with $x$ followed by $\rho g$ equal to $x$, one has $g = 1$. Then for every affine open $V \subseteq Y$ the open $\pi^{-1}V$ is affine, and, viewing $A := \Gamma(X,\pi^{-1}V)$ as an algebra over $A_0 := \Gamma(Y,V)$ via $\pi^\sharp_V$, there is a group homomorphism $\sigma : G \to \operatorname{Aut}_{\mathrm{ring}}(A)$ such that $\sigma g$ is the restriction of $(\rho g^{-1})^\sharp$ to $\pi^{-1}V$; $\sigma g$ fixes every element of the image of $A_0$; $A_0 \to A$ is injective; every element fixed by all $\sigma g$ lies in the image of $A_0$; and for every prime ideal $P$ of $A$ and every $g \neq 1$ there is $a \in A$ with $a - \sigma g\,a \notin P$.
--
--   This is the affine-chart form of the Galois data attached to the quotient of a scheme by a free action of a finite group: over an affine open of the quotient the ring of sections becomes a $G$-ring with the base as invariants and with trivial inertia at every prime. It feeds the finiteness, flatness and étaleness statement for such quotients and the local description of $\pi$ as a composite with automorphisms of $X$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient
    {X Y : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)
    (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hfib : ∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hinj : ∀ V : Y.Opens, Function.Injective (π.app V))
    (hrange : ∀ V : Y.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (hfree : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (g : G), x ≫ (ρ g).hom = x → g = 1)
    (V : Y.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen (π ⁻¹ᵁ V) ∧
    letI : Algebra Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
    ∃ σ : G →* (Γ(X, π ⁻¹ᵁ V) ≃+* Γ(X, π ⁻¹ᵁ V)),
      (∀ (g : G) (a : Γ(X, π ⁻¹ᵁ V)),
        σ g a = (ρ g⁻¹).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g⁻¹]) a) ∧
      (∀ (g : G) (r : Γ(Y, V)), σ g (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) = algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) ∧
      Function.Injective (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V)) ∧
      (∀ a : Γ(X, π ⁻¹ᵁ V), (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V))) ∧
      (∀ P : Ideal Γ(X, π ⁻¹ᵁ V), P.IsPrime → ∀ g : G, g ≠ 1 → ∃ a : Γ(X, π ⁻¹ᵁ V), a - σ g a ∉ P) := by sorry
