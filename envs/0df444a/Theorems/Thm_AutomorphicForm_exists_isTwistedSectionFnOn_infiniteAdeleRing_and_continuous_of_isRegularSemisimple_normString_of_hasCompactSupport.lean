-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/014fc7a5-acf9-5e7d-8ba8-26a336d3376a
-- title:
--   Continuous twisted sections at archimedean places
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma : L \simeq_{\mathrm{alg}[K]} L$ be a $K$-automorphism of $L$, and write $G = \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, where $\mathbb{A}_{K,\infty}$ is `InfiniteAdeleRing K`; the automorphism $\sigma$ acts on $G$ entrywise through the left tensor factor, giving the group homomorphism [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202). Let $\delta \in G$ and assume that its twisted norm $\prod_{i=0}^{[L:K]-1} \sigma_{\mathrm{GL}}^{i}(\delta)$, taken in the order given by `List.range (Module.finrank K L)`, is regular semisimple in the sense that $(\mathrm{tr})^2 - 4\det$ of the underlying matrix is a unit of $L \otimes_K \mathbb{A}_{K,\infty}$. Let $T = \{t \in G : t\,\delta\,\sigma_{\mathrm{GL}}(t)^{-1} = \delta\}$ be the $\sigma$-twisted centraliser of $\delta$, equipped with the Borel $\sigma$-algebra of its subspace topology, and let $\tau'$ be a Haar measure on $T$ for that $\sigma$-algebra. Let $\varphi : G \to \mathbb{C}$ be any function with compact support (no continuity or measurability being assumed). Then there exists $w : G \to \mathbb{R}$ which is everywhere nonnegative, Borel measurable, compactly supported, continuous, and satisfies $\int_{t \in T} w(tx)\,\mathrm{d}\tau'(t) = 1$ for every $x \in G$ with $\varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x)) \neq 0$.
--
--   The function $w$ is the normalising section used to turn a twisted orbital integral over the coset space $T \backslash G$ into an integral over $G$ itself; its existence at archimedean places rests on the closedness of the $\sigma$-conjugacy class of an element with regular semisimple norm. It is invoked in the construction of archimedean test functions and in the comparison of twisted weighted orbital integrals on $\mathrm{GL}_2$ with their Satake-type expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ']
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ δ τ' φ w ∧ Continuous w := by sorry
