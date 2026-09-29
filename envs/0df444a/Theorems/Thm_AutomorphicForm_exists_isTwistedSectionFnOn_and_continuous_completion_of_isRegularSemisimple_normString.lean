-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/b058844a-dcf3-53e0-9f22-437654b836c3
-- title:
--   Continuous twisted sections at an archimedean place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ that is Galois, let $\sigma$ be a $K$-algebra automorphism of $L$, and assume every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. Let $v$ be an infinite place of $K$, write $K_v$ for its completion, and let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$. Write $\sigma$ also for the map induced on $\mathrm{GL}_2(L \otimes_K K_v)$ by $\sigma \otimes \mathrm{id}$ acting entrywise. Assume the norm string $\delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$, where $n = [L:K]$, is regular semisimple in the sense that $(\mathrm{tr})^2 - 4\det$ of it is a unit of $L \otimes_K K_v$. Let $\tau'$ be a Haar measure, for the Borel $\sigma$-algebra of the subspace topology, on the twisted centraliser $\{t : t\delta\sigma(t)^{-1} = \delta\}$, and let $\varphi : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ have compact support. Then there is a continuous $W : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{R}$ that is everywhere nonnegative, Borel measurable, compactly supported, and satisfies $\int_{t} W(tx)\,\mathrm{d}\tau' = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$.
--
--   The function $W$ is a partition-of-unity (section) weight along the twisted conjugacy orbit of $\delta$: it normalises the fibres of the orbit map over the support of $\varphi$, and so allows a twisted orbital integral at an archimedean place to be unfolded against the centraliser measure $\tau'$. It is obtained from the corresponding statement over the infinite adele ring $L \otimes_K \mathbb{A}_{K,\infty}$ transported along the topological ring and group decompositions into the factors indexed by the infinite places of $K$, and it feeds the archimedean matching and twisted-orbital-integral comparison statements for scalar classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isRegularSemisimple_normString
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K)
    (δ : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : IsRegularSemisimple (normString K L v.Completion σ δ))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by sorry
