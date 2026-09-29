-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul
-- name    : AutomorphicForm.exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/fc14da0e-84ef-5770-92c4-24c2170b96b7
-- title:
--   Compactly controlled Hilbert 90 for GL₂ over the adeles
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\sigma : L \simeq_{\text{alg}[K]} L$ be a $K$-algebra automorphism of $L$. Write $G' = \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring `AdeleRing (𝓞 K) K`, and let $\sigma$ act on $G'$ by [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202), i.e. entrywise through the ring homomorphism $\sigma \otimes \mathrm{id}$ on $L \otimes_K \mathbb{A}_K$ (the functorial map $\mathrm{GL}_2$ of [`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199)). The assertion is: for every compact subset $C \subseteq G'$ there exists a compact subset $D \subseteq G'$ such that $$\{x \in G' : x^{-1}\,\sigma(x) \in C\} \subseteq F \cdot D,$$ where $F$ is the underlying set of the subgroup [`AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ 1`](def/AutomorphicForm_TwistedOrbital.html#L220), that is, the `sigmaCentralizer` of the element $1$ for the endomorphism `sigmaGL`: the subgroup $\{t \in G' : t \cdot 1 \cdot \sigma(t)^{-1} = 1\}$ of elements fixed by the $\sigma$-action, and the product $F \cdot D$ is the pointwise product of subsets of $G'$.
--
--   This is the compactly controlled form of Hilbert's Theorem 90 for $\mathrm{GL}_2$ over the adeles: the twisted Lang map $x \mapsto x^{-1}\sigma(x)$ is proper modulo the $\sigma$-fixed subgroup, so that compact sets pull back into finitely many fixed-group translates of a compact set. It supplies the properness needed to produce compactly supported twisted sections at twisted conjugacy classes of a scalar, and is used in [`AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar`](thm.html#AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          x⁻¹ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x ∈ C} ⊆
        ((AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ 1 :
            Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D := by sorry
