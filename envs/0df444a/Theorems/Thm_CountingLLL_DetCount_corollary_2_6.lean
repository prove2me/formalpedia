-- Prove2me | Theorems.Thm_CountingLLL_DetCount_corollary_2_6
-- name    : CountingLLL.DetCount.corollary_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:10.895747+00:00
-- url     : https://prove2.me/theorems/fac1aca9-04a3-460e-a154-fea59b7ddb1e
-- title:
--   Corollary 2.6 — rooted 2-trees of size $\ell$
-- statement:
--   Let $G=(V,E)$ be a graph in which every vertex has degree at most $\Delta$, and let $v\in V$. For every $\ell$, the number of 2-trees of $G$ of size $\ell$ containing $v$ (sets independent in $G$ and connected in $G^2$) is finite and at most
--   $$(\mathrm e\Delta^2)^{\ell-1}.$$
--
--   This is the combinatorial count behind the $pD^2$ scale of the paper and the enumeration cost in Lemma 4.1.
--
--   Differences from the source:
--   - generalization: a graph with maximum degree Δ → a locally finite simple graph on any vertex type (possibly infinite) whose degrees are at most Δ; finiteness of the family is part of the conclusion; reason: Δ = the maximum degree of a finite graph is a special case
--   - encoding: the exponent ℓ − 1 for the positive size of a rooted vertex set → natural subtraction ℓ - 1, also permitting ℓ = 0; reason: the exponents agree for every positive size; at ℓ = 0 the rooted family is empty and the displayed upper bound is 1
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Corollary 2.6, PDF p. 8 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_TwoTree

set_option autoImplicit false

namespace CountingLLL.DetCount

/-- Corollary 2.6: in a graph `G` (any vertex type, locally finite) whose vertex degrees are at
most `Δ`, for every vertex `v` and size `ℓ` the family of 2-trees of size `ℓ` containing `v` is
finite and has at most `(eΔ²)^{ℓ−1}` members. -/
theorem corollary_2_6 {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ)
    (hΔ : ∀ u, G.degree u ≤ Δ) (v : V) (ℓ : ℕ) :
    {S : Finset V | v ∈ S ∧ S.card = ℓ ∧ IsTwoTree G S}.Finite ∧
    (({S : Finset V | v ∈ S ∧ S.card = ℓ ∧ IsTwoTree G S}.ncard : ℕ) : ℝ) ≤
      (Real.exp 1 * (Δ : ℝ) ^ 2) ^ (ℓ - 1) := by sorry

end CountingLLL.DetCount
