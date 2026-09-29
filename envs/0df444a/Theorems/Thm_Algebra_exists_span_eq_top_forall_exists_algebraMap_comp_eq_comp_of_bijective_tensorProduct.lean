-- Prove2me | Theorems.Thm_Algebra_exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct
-- name    : Algebra.exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/0c8a3cef-816f-5a28-b060-9f5082f5dd3b
-- title:
--   Zariski-local splitting of two maps out of a Galois cover
-- statement:
--   Let $\mathcal{O}$ and $\mathcal{O}'$ be commutative rings with $\mathcal{O}'$ an $\mathcal{O}$-algebra, let $G$ be a finite group, and let $\tau : G \to (\mathcal{O}' \simeq_{\mathcal{O}} \mathcal{O}')$ be a group homomorphism into the group of $\mathcal{O}$-algebra automorphisms of $\mathcal{O}'$. Assume the map $\mathcal{O}' \otimes_{\mathcal{O}} \mathcal{O}' \to (G \to \mathcal{O}')$ sending $x$ to the family indexed by $\sigma \in G$ obtained by applying $\mathrm{id} \otimes \tau_\sigma$ to $x$ and then the multiplication map $\mathcal{O}' \otimes_{\mathcal{O}} \mathcal{O}' \to \mathcal{O}'$ (so that $a \otimes b \mapsto (a\,\tau_\sigma(b))_{\sigma}$) is bijective. Let $S$ be a commutative ring and $s_1, s_2 : \mathcal{O}' \to S$ ring homomorphisms whose restrictions to $\mathcal{O}$ agree, i.e. $s_1 \circ \mathrm{algebraMap}_{\mathcal{O}, \mathcal{O}'} = s_2 \circ \mathrm{algebraMap}_{\mathcal{O}, \mathcal{O}'}$. Then there exist a natural number $k$ and elements $r : \mathrm{Fin}\,k \to S$ whose range generates the unit ideal of $S$, such that for every index $i$ there is $\sigma \in G$ with $s_2$ and $s_1 \circ \tau_\sigma$ becoming equal after composition with the localisation map $S \to S[1/r_i]$, i.e. $s_2(y) = s_1(\tau_\sigma(y))$ in $\mathrm{Localization.Away}\,(r_i)$ for all $y \in \mathcal{O}'$.
--
--   This is the standard local-torsor property of a Galois cover: if $\mathcal{O} \to \mathcal{O}'$ is Galois with group $G$ in the sense that $\mathcal{O}' \otimes_{\mathcal{O}} \mathcal{O}' \cong \prod_{\sigma \in G} \mathcal{O}'$ via $a \otimes b \mapsto (a\,\tau_\sigma b)_\sigma$, then any two $\mathcal{O}$-algebra maps $\mathcal{O}' \to S$ differ, Zariski-locally on $\mathrm{Spec}\,S$, by an element of $G$. It is used in the construction of a cyclotomic Galois cover, via [`Algebra.exists_cyclotomic_galois_cover_of_isUnit`](thm.html#Algebra.exists_cyclotomic_galois_cover_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct
    (𝒪 : Type u) [CommRing 𝒪] (𝒪' : Type u) [CommRing 𝒪'] [Algebra 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (S : Type u) [CommRing S] (s₁ s₂ : 𝒪' →+* S)
    (hs : s₁.comp (algebraMap 𝒪 𝒪') = s₂.comp (algebraMap 𝒪 𝒪')) :
    ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
      (algebraMap S (Localization.Away (r i))).comp s₂ =
        (algebraMap S (Localization.Away (r i))).comp (s₁.comp ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) := by sorry
