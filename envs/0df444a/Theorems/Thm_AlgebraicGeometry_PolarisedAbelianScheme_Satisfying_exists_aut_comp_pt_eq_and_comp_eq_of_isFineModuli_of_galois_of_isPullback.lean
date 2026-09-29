-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/8d03ca83-352f-5bc6-88a8-29a8d3e6db90
-- title:
--   Finite group action on a fine moduli scheme
-- statement:
--   Fix natural numbers $g,d,n$ and a property $Q$ of polarised abelian schemes of type $(g,d,n)$ (an object over $S$ consisting of $A \to \operatorname{Spec} S$ with a commutative relative group law, the abelian-scheme property bundle, fibres of topological Krull dimension $g$, a family of $2g$ $n$-torsion sections that is independent and spans the $n$-torsion on geometric fibres, and an invertible module with closed immersion by sections whose geometric fibre $H^0$ has rank $d$), assumed stable under base change: for every ring map $\varphi : S \to S'$ and objects $u,u'$ with $u'$ a pullback of $u$ along $\varphi$, $Q\,S\,u$ implies $Q\,S'\,u'$. Let $\mathcal O'$ be a commutative algebra over a commutative ring $\mathcal O$, let $G$ be a finite group, and let $\tau : G \to \operatorname{Aut}_{\mathcal O}(\mathcal O')$ be a group homomorphism. Assume the action is Galois in the following sense: for every commutative ring $S$ and morphisms $s_1,s_2 : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O'$ whose composites with $\operatorname{Spec}$ of $\mathcal O \to \mathcal O'$ agree, there are finitely many $r_i \in S$ generating the unit ideal such that, after restriction to each $\operatorname{Spec}$ of the localisation away from $r_i$, $s_2$ equals $s_1$ followed by $\operatorname{Spec}(\tau\sigma)$ for some $\sigma \in G$. Let $M'$ be a scheme with $\pi_{M'} : M' \to \operatorname{Spec}\mathcal O'$ and let $\mathrm{pt}'$ assign to each ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O'$ and each pair $X$ of an object of type $(g,d,n)$ over $S$ together with a proof of $Q$ a morphism $\operatorname{Spec} S \to M'$ over $s$; assume $(M',\pi_{M'},\mathrm{pt}')$ is a fine moduli datum, i.e. $\mathrm{pt}'$ is constant on isomorphism classes, compatible with pullbacks along ring maps, and for each $(S,s)$ induces a bijection onto the morphisms $\operatorname{Spec} S \to M'$ over $s$ (surjectivity, and injectivity up to isomorphism of objects). Then there is a family $\rho : G \to (M' \cong M')$ of automorphisms with $\rho_1 = \mathrm{id}_{M'}$, $\rho_{\sigma\sigma'} = \rho_\sigma$ followed by $\rho_{\sigma'}$, $\rho_\sigma$ followed by $\pi_{M'}$ equal to $\pi_{M'}$ followed by $\operatorname{Spec}(\tau\sigma)$, and $\mathrm{pt}'_{S,s}(X)$ followed by $\rho_\sigma$ equal to $\mathrm{pt}'_{S,\,s\,\text{followed by}\,\operatorname{Spec}(\tau\sigma)}(X)$ for all $\sigma, S, s, X$; moreover, for every scheme $M$ and every $q : M' \to M$ with $\rho_\sigma$ followed by $q$ equal to $q$ for all $\sigma$, and all $s_1,s_2$ agreeing over $\mathcal O$ as above, $\mathrm{pt}'_{S,s_1}(X)$ followed by $q$ equals $\mathrm{pt}'_{S,s_2}(X)$ followed by $q$.
--
--   This is the descent step in the construction of a moduli scheme over the smaller base: the Galois group of $\mathcal O'/\mathcal O$ acts on a fine moduli scheme over $\mathcal O'$ through the twisting of the structure morphism, and moduli points of a single object over $\mathcal O$ become independent of the chosen $\mathcal O'$-structure once one composes with an invariant morphism. It is used in the passage from fine moduli schemes over rings containing suitable roots of unity to a fine moduli scheme over the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback
    (g d n : ℕ) (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    (hQbc : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    (𝒪 : Type) [CommRing 𝒪] (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))

    (hgal : ∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
      s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) →
      ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₂ =
          Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₁ ≫
            Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')))
    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
      PolarisedAbelianScheme.Satisfying g d n Q S → SchemeHomOver s πM')
    (hM' : PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M' πM' pt') :
    ∃ ρ : G → (M' ≅ M'),
      (ρ 1).hom = 𝟙 M' ∧ (∀ σ σ' : G, (ρ (σ * σ')).hom = (ρ σ).hom ≫ (ρ σ').hom) ∧
      (∀ σ : G, (ρ σ).hom ≫ πM' = πM' ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) ∧
      (∀ (σ : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪'))
        (X : PolarisedAbelianScheme.Satisfying g d n Q S),
        (pt' S s X).1 ≫ (ρ σ).hom = (pt' S (s ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) X).1) ∧
      (∀ (M : Scheme.{0}) (q : M' ⟶ M), (∀ σ : G, (ρ σ).hom ≫ q = q) →
        ∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
          s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) →
          ∀ X : PolarisedAbelianScheme.Satisfying g d n Q S, (pt' S s₁ X).1 ≫ q = (pt' S s₂ X).1 ≫ q) := by sorry
