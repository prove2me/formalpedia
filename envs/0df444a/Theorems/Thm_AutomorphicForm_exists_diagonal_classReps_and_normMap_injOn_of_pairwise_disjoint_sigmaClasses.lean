-- Prove2me | Theorems.Thm_AutomorphicForm_exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses
-- name    : AutomorphicForm.exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/d04dfe05-3948-526d-ad9c-26df5bd49f81
-- title:
--   Diagonal representatives over K and the norm map on σ-classes
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ is an integral power of $\sigma$ (so $\mathrm{Gal}(L/K)$ is cyclic with generator $\sigma$), and let it be recorded that every $K$-automorphism of $K$ is a power of the identity. Let $\Delta \subseteq \mathrm{GL}_2(L)$ be a set such that: each $t \in \Delta$ has vanishing $(1,0)$ and $(0,1)$ entries and satisfies $N_{L/K}(t_{00}/t_{11}) \neq 1$; for distinct $t,t' \in \Delta$ the sets $S(t) = \{\delta : \exists g,\ t^{-1}(g^{-1}\delta\,\sigma(g)) \in Z(\mathrm{GL}_2(L))\}$ and $S(t')$ are disjoint; and the set of $\delta \in \mathrm{GL}_2(L)$ for which `normClassMap hgen` sends the $\sigma$-conjugacy class of $\delta$ to the conjugacy class of some $\gamma \in \mathrm{GL}_2(K)$ whose characteristic polynomial factors as $(X-a)(X-b)$ with $a \neq b$ in $K$ is contained in $\bigcup_{t \in \Delta} S(t)$. The conclusion asserts the existence of a set $\Delta_K \subseteq \mathrm{GL}_2(K)$ and a map $n : \mathrm{GL}_2(L) \to \mathrm{GL}_2(K)$ with the same three properties over $K$ for the identity automorphism of $K$ in place of $\sigma$ (off-diagonal entries vanishing and $\mathrm{norm}_K(\gamma_{00}/\gamma_{11}) \neq 1$; pairwise disjointness of the corresponding centre-saturated conjugacy classes; and covering of the elements with hyperbolic norm class), together with: for each $t \in \Delta$, $n(t) \in \Delta_K$ is diagonal with entries $N_{L/K}(t_{00})$ and $N_{L/K}(t_{11})$; $n$ is injective on $\Delta$; and every $\gamma \in \Delta_K$ whose ratio $\gamma_{00}/\gamma_{11}$ lies in the image of $N_{L/K} : L \to K$ equals $n(t)$ for some $t \in \Delta$.
--
--   This is the transfer, along the norm map of a cyclic extension, of a system of diagonal representatives for centre-saturated $\sigma$-twisted hyperbolic classes over $L$ to a system of representatives of the corresponding ordinary classes over $K$, in the style of the hyperbolic matching in base change for $\mathrm{GL}_2$; the final surjectivity clause isolates the representatives over $K$ whose ratio is a global norm, so that the remaining ones have non-normic ratio. It is used in the comparison of hyperbolic terms, in the two results on hyperbolic slopes and winding data for matching eigensystems that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Pointwise

theorem AutomorphicForm.exists_diagonal_classReps_and_normMap_injOn_of_pairwise_disjoint_sigmaClasses
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hgenK : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    (hΔcov : {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∃ (ΔK : Set (GL (Fin 2) K)) (n : GL (Fin 2) L → GL (Fin 2) K),
      (∀ t ∈ ΔK, (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1) ∧
      (∀ t ∈ ΔK, ∀ t' ∈ ΔK, t ≠ t' →
        Disjoint {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
          {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}) ∧
      ({δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
          LT.TwistedNorm.normClassMap hgenK (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} ⊆
        ⋃ t ∈ ΔK, {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
            t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}) ∧
      (∀ t ∈ Δ, n t ∈ ΔK ∧
        (n t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (n t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        (n t : Matrix (Fin 2) (Fin 2) K) 0 0 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
        (n t : Matrix (Fin 2) (Fin 2) K) 1 1 = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∧
      (∀ t ∈ Δ, ∀ t' ∈ Δ, n t = n t' → t = t') ∧
      (∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈
          Set.range (Algebra.norm K : L → K) → ∃ t ∈ Δ, n t = γ) := by sorry
