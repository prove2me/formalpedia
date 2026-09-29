-- Prove2me | Theorems.Thm_Algebra_exists_cyclotomic_galois_cover_of_isUnit
-- name    : Algebra.exists_cyclotomic_galois_cover_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/11198771-23bf-583f-ae10-7825acad7c24
-- title:
--   Cyclotomic Galois cover adjoining a primitive m-th root
-- statement:
--   Let $\mathcal O$ be a commutative ring, and let $m$ be a natural number with $0 < m$ such that the image of $m$ in $\mathcal O$ is a unit. Then there exist a type $\mathcal O'$ with a commutative ring structure and an $\mathcal O$-algebra structure such that: $\mathcal O'$ is finite, free and faithfully flat as an $\mathcal O$-module; there is $\zeta \in \mathcal O'$ with $\zeta^m = 1$ and with $1 - \zeta^j$ a unit of $\mathcal O'$ for every $j$ with $0 < j < m$; for every commutative ring $S$ that is an $\mathcal O$-algebra, $S \otimes_{\mathcal O} \mathcal O'$ is faithfully flat and étale over $S$; and there exist a finite group $G$ and a monoid homomorphism $\tau$ from $G$ to the group of $\mathcal O$-algebra automorphisms of $\mathcal O'$ such that (i) the map $\mathcal O' \otimes_{\mathcal O} \mathcal O' \to \prod_{\sigma \in G} \mathcal O'$ whose $\sigma$-component is multiplication in $\mathcal O'$ composed with $\mathrm{id} \otimes \tau(\sigma)$, i.e. $s \otimes t \mapsto (s\,\tau(\sigma)(t))_{\sigma}$, is bijective, and (ii) for every commutative ring $S$ and any two morphisms $s_1, s_2 \colon \operatorname{Spec} S \to \operatorname{Spec} \mathcal O'$ whose composites with $\operatorname{Spec}$ of the structure map $\mathcal O \to \mathcal O'$ agree, there are $k \in \mathbb N$ and $r \colon \mathrm{Fin}\,k \to S$ with $(r_i)_i$ generating the unit ideal of $S$, such that for each $i$ there is $\sigma \in G$ with the restriction of $s_2$ along $\operatorname{Spec}$ of $S \to S_{r_i}$ equal to the restriction of $s_1$ followed by $\operatorname{Spec}(\tau(\sigma))$.
--
--   This packages the cyclotomic extension $\mathcal O[X]/(\Phi_m)$ of a ring in which $m$ is invertible as a finite free faithfully flat Galois cover with group $(\mathbb Z/m)^\times$, carrying an $m$-th root of unity $\zeta$ all of whose nontrivial powers satisfy $1 - \zeta^j \in (\mathcal O')^\times$. It is used to descend the existence of a fine moduli space for polarised abelian schemes from bases carrying a primitive $m$-th root of unity to arbitrary bases, via [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_forall_exists_isFineModuli_of_primitiveRoot`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_forall_exists_isFineModuli_of_primitiveRoot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_cyclotomic_galois_cover_of_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem Algebra.exists_cyclotomic_galois_cover_of_isUnit
    (𝒪 : Type) [CommRing 𝒪] (m : ℕ) (hm : 0 < m) (hmu : IsUnit ((m : ℕ) : 𝒪)) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : Algebra 𝒪 𝒪'),
      Module.Finite 𝒪 𝒪' ∧ Module.Free 𝒪 𝒪' ∧ Module.FaithfullyFlat 𝒪 𝒪' ∧
      (∃ ζ : 𝒪', ζ ^ m = 1 ∧ ∀ j : ℕ, 0 < j → j < m → IsUnit (1 - ζ ^ j)) ∧
      (∀ (S : Type) [CommRing S] [Algebra 𝒪 S], Module.FaithfullyFlat S (S ⊗[𝒪] 𝒪') ∧ Algebra.Etale S (S ⊗[𝒪] 𝒪')) ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G) (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪')),
        (Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
          Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
            (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x)) ∧
        (∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
          s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) →
          ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
            Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₂ =
              Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₁ ≫
                Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) := by sorry
