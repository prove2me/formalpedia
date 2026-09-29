-- Prove2me | Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified
-- name    : AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/75787c12-6502-5603-aaa9-9f8b7aa93db3
-- title:
--   Ramified real place model: L⊗_K Kᵥ≅ℂ⊗_ℝℝ
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, and let $w$ be an infinite place of $L$ which is ramified over $K$, i.e. satisfies `InfinitePlace.IsRamified`; write $v = w \circ \operatorname{algebraMap} K L$ for the restricted place of $K$ and $K_v$ for its completion. The assertion is that there exist a ring isomorphism $e \colon K_v \to \mathbb{R}$ and a ring isomorphism $E \colon L \otimes_K K_v \to \mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}$ (tensor products formed with the right-action conventions) such that: $e$, $e^{-1}$, $E$ and $E^{-1}$ are all continuous; $E$ intertwines $\sigma \otimes \mathrm{id}_{K_v}$ with $\mathrm{conj} \otimes \mathrm{id}_{\mathbb{R}}$, that is $E(\sigma \otimes \mathrm{id})(z) = (\mathrm{conj} \otimes \mathrm{id})(E z)$ for all $z$, where $\mathrm{conj}$ is `Complex.conjAe`; for every $g \in \mathrm{GL}_2(K_v)$, applying $E$ entrywise to the image of $g$ under the entrywise map induced by $a \mapsto 1 \otimes a \colon K_v \to L \otimes_K K_v$ gives the image of the entrywise $e$-transform of $g$ under the corresponding map $\mathrm{GL}_2(\mathbb{R}) \to \mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$; $E$ is pinned on pure tensors, namely under the canonical identification $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R} \cong \mathbb{C}$ one has $E(x \otimes a) = w(x)\, e(a)$ for $x \in L$, $a \in K_v$, with $w(x)$ the chosen complex embedding `InfinitePlace.embedding` attached to $w$ and $e(a) \in \mathbb{R} \subset \mathbb{C}$; and finally $e(\operatorname{algebraMap} K\, K_v\, k) = w(\operatorname{algebraMap} K L\, k)$ in $\mathbb{C}$ for every $k \in K$.
--
--   This is the archimedean local model at a place of a quadratic extension $L/K$ where a real place $v$ of $K$ becomes a single complex place $w$ of $L$: the completion $K_v$ is $\mathbb{R}$, the base change $L \otimes_K K_v$ is $\mathbb{C}$ (written as $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}$ so that both sides have the same tensor shape), and the nontrivial automorphism $\sigma$ becomes complex conjugation. The explicit pinning conditions on pure tensors, on scalars from $K$ and on $\mathrm{GL}_2$ make the pair $(e, E)$ usable as a fixed identification in the archimedean matching and twisted-section constructions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K) :
    ∃ (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ)
      (E : L ⊗[K] (w.comap (algebraMap K L)).Completion ≃+* ℂ ⊗[ℝ] ℝ),
      Continuous e ∧ Continuous e.symm ∧ Continuous E ∧ Continuous E.symm ∧
      (∀ z, E (sigmaTensor K L (w.comap (algebraMap K L)).Completion σ z) =
        sigmaTensor ℝ ℂ ℝ Complex.conjAe (E z)) ∧
      (∀ g : GL (Fin 2) (w.comap (algebraMap K L)).Completion,
        Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L (w.comap (algebraMap K L)).Completion g) =
          toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.map e.toRingHom g)) ∧
      (∀ (x : L) (a : (w.comap (algebraMap K L)).Completion),
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)) (E (x ⊗ₜ a)) = w.embedding x * (e a : ℂ)) ∧
      (∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k)) := by sorry
