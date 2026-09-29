-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul
-- name    : AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a8e7f325-1e37-5db2-b5e6-5eb50fd13daa
-- title:
--   Properness of the twisted orbit map on the adelic centralizer of a regular semisimple norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra that is finite-dimensional over $K$, put $n = \operatorname{finrank}_K L$ and write $\mathbb{A}_K$ for the adele ring `AdeleRing (𝓞 K) K`. Let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma^{n} = 1$, and let $\sigma$ act on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ entrywise through the ring homomorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K \mathbb{A}_K$; this action on $\mathrm{GL}_2$ is [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202). For $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ let $N\delta = \delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$ be the norm string, the product over $i = 0, \dots, n-1$ of the $i$-th iterate of the $\sigma$-action applied to $\delta$. Assume $N\delta$ is regular semisimple in the sense of the project, namely that $\operatorname{tr}(N\delta)^2 - 4 \det(N\delta)$ is a unit of $L \otimes_K \mathbb{A}_K$. Then for every compact set $C \subseteq \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ there is a compact set $D$ in the same group such that the set of $z$ lying in the centralizer of the singleton $\{N\delta\}$ and satisfying $z^{-1} \delta \, \sigma(z) \in C$ is contained in $T' \cdot D$, where $T'$ is the twisted centralizer $\{t : t \delta \sigma(t)^{-1} = \delta\}$ of $\delta$.
--
--   This is the properness, modulo the twisted centralizer, of the twisted orbit map $z \mapsto z^{-1}\delta\,\sigma(z)$ restricted to the adelic centralizer torus of a regular semisimple norm, the finiteness input needed for twisted orbital integrals in the base-change comparison for $\mathrm{GL}_2$. It is obtained by combining the corresponding statement over Artinian coefficient rings with the semi-local integrality estimate at unramified places, and is used in the construction of continuous twisted section functions over the adeles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {z : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          z ∈ Subgroup.centralizer
              ({AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ} :
                Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∧
            z⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ z ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ :
            Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D := by sorry
