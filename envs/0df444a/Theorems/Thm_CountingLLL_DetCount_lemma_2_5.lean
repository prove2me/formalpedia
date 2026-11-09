-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_2_5
-- name    : CountingLLL.DetCount.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:31.665232+00:00
-- url     : https://prove2.me/theorems/36935003-c9e2-4f67-a7fb-de28527e9e62
-- title:
--   Lemma 2.5 — rooted connected induced subgraphs [BCKL13]
-- statement:
--   Let $G=(V,E)$ be a graph in which every vertex has degree at most $\Delta$, and let $v\in V$. For every $\ell$, the number of connected induced subgraphs of size $\ell$ containing $v$ is finite and at most
--   $$(\mathrm e\Delta)^{\ell-1}.$$
--
--   It bounds the number of terms of size $\ell$ in a cluster-type expansion; applied to the square graph it gives Corollary 2.6.
--
--   Differences from the source:
--   - generalization: a graph with maximum degree Δ → a locally finite simple graph on any vertex type (possibly infinite) whose degrees are at most Δ; finiteness of the family is part of the conclusion; reason: Δ = the maximum degree of a finite graph is a special case
--   - encoding: connected induced subgraphs of size ℓ containing v → vertex sets S of size ℓ with v ∈ S and G[S] connected; reason: an induced subgraph is determined by its vertex set
--   - encoding: the exponent ℓ − 1 for the positive size of a rooted vertex set → natural subtraction ℓ - 1, also permitting ℓ = 0; reason: the exponents agree for every positive size; at ℓ = 0 the rooted family is empty and the displayed upper bound is 1
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 2.5 ([BCKL13]), PDF p. 8 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

set_option autoImplicit false

namespace CountingLLL.DetCount

/-- Lemma 2.5 ([BCKL13]): in a graph `G` (any vertex type, locally finite) whose vertex degrees
are at most `Δ`, for every vertex `v` and size `ℓ` the family of vertex sets of size `ℓ`
containing `v` and inducing a connected subgraph is finite and has at most `(eΔ)^{ℓ−1}` members. -/
theorem lemma_2_5 {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ)
    (hΔ : ∀ u, G.degree u ≤ Δ) (v : V) (ℓ : ℕ) :
    {S : Finset V | v ∈ S ∧ S.card = ℓ ∧ (G.induce (S : Set V)).Connected}.Finite ∧
    (({S : Finset V | v ∈ S ∧ S.card = ℓ ∧ (G.induce (S : Set V)).Connected}.ncard : ℕ) : ℝ) ≤
      (Real.exp 1 * Δ) ^ (ℓ - 1) := by sorry

end CountingLLL.DetCount
