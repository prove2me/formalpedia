-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action
-- name    : AlgebraicGeometry.Scheme.isPullback_of_quotient_of_galois_of_finite_action
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/727df1da-3dab-5dd3-bbac-b8244be1c5f8
-- title:
--   Galois descent: an invariant affine quotient square is cartesian
-- statement:
--   Let $\mathcal O$ and $\mathcal O'$ be commutative rings in `Type` with $\mathcal O'$ an $\mathcal O$-algebra that is finite, free and faithfully flat as an $\mathcal O$-module, let $G$ be a finite group, and let $\tau : G \to (\mathcal O' \simeq_{\mathcal O} \mathcal O')$ be a group homomorphism into the $\mathcal O$-algebra automorphisms of $\mathcal O'$, subject to the Galois condition `hgal`: the map $\mathcal O' \otimes_{\mathcal O} \mathcal O' \to (G \to \mathcal O')$ sending $x$ to the family indexed by $\sigma$ whose $\sigma$-component is obtained by applying $\tau\sigma$ to the right tensor factor and then multiplying out, is bijective. Let $M'$ be a scheme with a morphism $\pi_{M'} : M' \to \operatorname{Spec}\mathcal O'$, and let $\rho$ assign to each $\sigma \in G$ a self-isomorphism of $M'$ with $\rho_1 = \mathrm{id}$, $\rho_{\sigma\sigma'} = \rho_\sigma$ followed by $\rho_{\sigma'}$, and $\rho_\sigma$ followed by $\pi_{M'}$ equal to $\pi_{M'}$ followed by $\operatorname{Spec}(\tau\sigma)$. Let $M$ be a scheme with $\pi_M : M \to \operatorname{Spec}\mathcal O$ and $q : M' \to M$ such that $\rho_\sigma$ followed by $q$ is $q$ for every $\sigma$, $q$ followed by $\pi_M$ equals $\pi_{M'}$ followed by $\operatorname{Spec}$ of the structure map $\mathcal O \to \mathcal O'$, $q$ is an affine morphism, and for every open $V \subseteq M$ the ring map $q$ induces on sections over $V$ is injective with image exactly the sections of $q^{-1}V$ fixed by the maps induced by all $\rho_\sigma$ on $q^{-1}V$. Then the square formed by $q$, $\pi_{M'}$, $\pi_M$ and $\operatorname{Spec}(\mathcal O \to \mathcal O')$ is cartesian, i.e. $M'$ is the fibre product $M \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec}\mathcal O'$ via $q$ and $\pi_{M'}$.
--
--   This is the geometric form of Galois descent for a free action of a finite group over a Galois extension of base rings: the hypotheses on $q$ are exactly the defining properties of the quotient of $M'$ by $G$ as a scheme whose sections are the invariant sections, and the conclusion identifies $M'$ with the base change of that quotient along $\mathcal O \to \mathcal O'$. It is the cartesianness half of [`AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action`](thm.html#AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action), and rests on the affine descent statement [`Algebra.bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois`](thm.html#Algebra.bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u v

theorem AlgebraicGeometry.Scheme.isPullback_of_quotient_of_galois_of_finite_action
    (𝒪 : Type) [CommRing 𝒪] (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [Module.Free 𝒪 𝒪']
    [Module.FaithfullyFlat 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (ρ : G → (M' ≅ M')) (hρ1 : (ρ 1).hom = 𝟙 M') (hρmul : ∀ σ σ' : G, (ρ (σ * σ')).hom = (ρ σ).hom ≫ (ρ σ').hom)
    (hρπ : ∀ σ : G, (ρ σ).hom ≫ πM' = πM' ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : M' ⟶ M)
    (hq : ∀ σ : G, (ρ σ).hom ≫ q = q)
    (hqπ : q ≫ πM = πM' ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')))
    (haff : IsAffineHom q)
    (hinj : ∀ V : M.Opens, Function.Injective (q.app V))
    (hrange : ∀ V : M.Opens, Set.range (q.app V) =
      {t | ∀ σ : G, (ρ σ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hq σ]) t = t}) :
    CategoryTheory.IsPullback q πM' πM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))) := by sorry
