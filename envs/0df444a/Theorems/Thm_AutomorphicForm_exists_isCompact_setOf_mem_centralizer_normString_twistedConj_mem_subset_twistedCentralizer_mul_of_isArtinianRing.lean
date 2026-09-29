-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
-- name    : AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/96316c2c-c25a-5b95-aaec-33590dfe667a
-- title:
--   Properness of the twisted orbit map modulo the twisted centraliser
-- statement:
--   Let $L/K$ be an extension of fields with $L$ finite-dimensional over $K$, set $n = \dim_K L$, and let $A$ be a commutative $K$-algebra carrying a Hausdorff, locally compact, second countable topological ring structure and which is Artinian as a ring; assume $L \otimes_K A$ is reduced. Let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma^{n} = 1$, and let $\sigma$ act on $G = \mathrm{GL}_2(L \otimes_K A)$ entrywise through the ring homomorphism $\sigma \otimes \mathrm{id}_A$ ([`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202)). For $\delta \in G$ put $N\delta = \delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$ ([`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205), the ordered product over $i \in \{0,\dots,n-1\}$ of the $i$-fold iterates), and assume $N\delta$ is regular semisimple in the sense that $\operatorname{tr}(N\delta)^2 - 4\det(N\delta)$ is a unit of $L \otimes_K A$. Then for every compact $C \subseteq G$ there is a compact $D \subseteq G$ such that every $z \in G$ lying in the centraliser of $\{N\delta\}$ and satisfying $z^{-1}\delta\,\sigma(z) \in C$ belongs to the product set $T' \cdot D$, where $T' = \{t \in G : t\,\delta\,\sigma(t)^{-1} = \delta\}$ is the twisted centraliser of $\delta$.
--
--   This is the local properness statement underlying the convergence of twisted orbital integrals at a regular element in cyclic base change for $\mathrm{GL}_2$: on the centraliser of the norm $N\delta$, the twisted orbit map $z \mapsto z^{-1}\delta\,\sigma(z)$ has compact fibres modulo the twisted centraliser. It is used in the corresponding statement without the Artinian hypothesis on $A$ and in the construction of continuous, compactly supported twisted section functions attached to a regular semisimple norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [IsArtinianRing A]
    [IsReduced (L ⊗[K] A)]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (C : Set (GL (Fin 2) (L ⊗[K] A))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] A)), IsCompact D ∧
      {z : GL (Fin 2) (L ⊗[K] A) |
          z ∈ Subgroup.centralizer
              ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
            z⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ z ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) * D := by sorry
