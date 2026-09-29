-- Prove2me | Theorems.Thm_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor
-- name    : AutomorphicForm.mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/eee5f7b3-18bd-5005-bf15-7a3ee2e6003c
-- title:
--   Coordinatewise splitting of the archimedean twisted commutant
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\Xi : L \otimes_K \mathbb{A}_{K,\infty} \to \prod_{w \mid \infty} L \otimes_K K_w$ be a ring isomorphism (the product over the infinite places of $K$, with $K_w$ the completion) such that $\Xi(x \otimes a)_w = x \otimes a_w$ for all $x \in L$, $a \in \mathbb{A}_{K,\infty}$ and all $w$. Fix $\mathbb{R}$-algebra structures on the factors $L \otimes_K K_w$ and assume $\Xi$ is $\mathbb{R}$-linear, the $\mathbb{R}$-structure on $L \otimes_K \mathbb{A}_{K,\infty}$ being the one obtained from $\mathbb{R} \to$ mixed space $\cong \mathbb{A}_{K,\infty}$ followed by $a \mapsto 1 \otimes a$. Let $\delta \in M_2(L \otimes_K \mathbb{A}_{K,\infty})$ and let $\delta_w \in M_2(L \otimes_K K_w)$ be matrices with $\Xi(\delta_{ij})_w = (\delta_w)_{ij}$ for all $w, i, j$. Write $\sigma_A$ for the ring endomorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K A$. Suppose $e_1, \dots, e_{n_2} \in M_2(L \otimes_K \mathbb{A}_{K,\infty})$ are $\mathbb{R}$-linearly independent with $\mathbb{R}$-span exactly $\{X \mid X\delta = \delta\, \sigma_{\mathbb{A}_{K,\infty}}(X)\}$ (entrywise application of $\sigma_A$). Then the matrices $\Xi(e_a)$, obtained by applying $\Xi$ entrywise, are $\mathbb{R}$-linearly independent, and a matrix $X \in M_2(\prod_w L \otimes_K K_w)$ lies in their $\mathbb{R}$-span if and only if for every infinite place $w$ the $w$-component $X_w$ lies in the $\mathbb{R}$-span of $\{Y \in M_2(L \otimes_K K_w) \mid Y \delta_w = \delta_w\, \sigma_{K_w}(Y)\}$.
--
--   This is the archimedean place-by-place description of the $\sigma$-twisted commutant of $\delta$ in $M_2$: a basis of the twisted commutant over $L \otimes_K \mathbb{A}_{K,\infty}$ transports under $\Xi$ to a spanning family whose members are characterised by their local conditions at each infinite place. It is used in the archimedean comparison of twisted orbital integrals with orbital integrals, in [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.mem_span_map_ringEquiv_pi_iff_of_span_eq_setOf_mul_eq_mul_map_sigmaTensor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((w : InfinitePlace K) → L ⊗[K] w.Completion))
    (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace K), Ξ (x ⊗ₜ a) w = x ⊗ₜ (a w))
    [algE : ∀ w : InfinitePlace K, Algebra ℝ (L ⊗[K] w.Completion)]
    (hΞr : ∀ (r : ℝ) (z : L ⊗[K] InfiniteAdeleRing K),
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      Ξ (r • z) = r • Ξ z)
    (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (δw : ∀ w : InfinitePlace K, Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion))
    (hδw : ∀ (w : InfinitePlace K) (i j : Fin 2), Ξ (δ i j) w = δw w i j)
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hL :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      LinearIndependent ℝ e₂ ∧
        (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          {X | X * δ = δ * X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)}) :
    LinearIndependent ℝ (fun a => (e₂ a).map Ξ) ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ((w : InfinitePlace K) → L ⊗[K] w.Completion),
        X ∈ Submodule.span ℝ (Set.range (fun a => (e₂ a).map Ξ)) ↔
          ∀ w : InfinitePlace K,
            X.map (Pi.evalRingHom (fun w : InfinitePlace K => L ⊗[K] w.Completion) w) ∈
              Submodule.span ℝ {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.Completion) |
                Y * δw w = δw w * Y.map (AutomorphicForm.sigmaTensor K L w.Completion σ)} := by sorry
