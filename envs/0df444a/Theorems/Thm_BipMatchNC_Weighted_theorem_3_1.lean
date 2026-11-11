-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_theorem_3_1
-- name    : BipMatchNC.Weighted.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:14:40.558024+00:00
-- url     : https://prove2.me/theorems/a863cc4e-d96f-4794-9898-894d726f597d
-- title:
--   Theorem 3.1: a balanced bipartite graph has a perfect matching iff its matching matrix M(G) has full row rank
-- statement:
--   Let $F$ be a field and $G$ a balanced bipartite graph on $[n]+[n]$. Let $\gamma\in F$ have order at least $nr$, let $\alpha_1,\dots,\alpha_{n^2}\in F$ be such that the $n^2r$ elements $\alpha_j\gamma^\ell$ ($1\le j\le n^2$, $0\le\ell\le r-1$) are distinct, and let $\delta\ge n$, $r>n^2\delta$ and $D=n(r-\delta)$. Then
--   $$G\in\mathrm{PM}\iff \operatorname{rank}M(G)=nD,$$
--   i.e. the $nD\times n^2r$ matching matrix has full row rank.
--
--   This is a deterministic, rank-based characterization of bipartite perfect matching (a derandomization of Lovász's determinant test), and it yields the $\mathrm{NC}^2$ decision algorithm of Corollary 3.3. The paper's example choice is $\delta=n$, $r=n^3+1$, $\gamma$ of order $n^2r$ and $\alpha_j=\gamma^{r(j-1)}$; these are not hypotheses.
--
--   Differences from the source:
--   - reading: M(G) has full rank → Matrix.rank M(G) = n * D (full row rank); reason: M(G) has nD rows and n²r ≥ nD columns; the proof shows and uses full row rank
--   - encoding: §3.1 parameters: γ ∈ F of order at least nr; α_1, …, α_{n²} with the n²r elements α_jγ^ℓ (0 ≤ ℓ ≤ r − 1) distinct; δ ≥ n and r > n²δ; D = n(r − δ) → hypotheses OrderAtLeast γ (n * r), injectivity of (j, ℓ) ↦ α j * γ ^ ℓ on Fin (n * n) × Fin r, n ≤ δ, n ^ 2 * δ < r, and D written as n * (r - δ); reason: the standing assumptions of §3.1 (p. 9), stated as binders; F is an arbitrary field; under these hypotheses r > δ whenever n ≥ 1, so the ℕ-subtraction in D never truncates
--   - encoding: vertices u_1, …, u_n, v_1, …, v_n and column blocks 1, …, n² (1-based) → Fin n and Fin (n * n), 0-based; G as its bi-adjacency matrix BipGraph n; reason: indexing convention only
--   - encoding: G ∈ PM → G.HasPM: some permutation π with every (i, π i) an edge; reason: for balanced G a perfect matching is a permutation (p. 4)
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 10 (PDF 11), Theorem 3.1

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded
import Definitions.Def_BipMatchNC_Weighted_Graph
import Definitions.Def_BipMatchNC_Weighted_MatchingMatrix

namespace BipMatchNC.Weighted

theorem theorem_3_1 {F : Type*} [Field F] (n r δ : ℕ) (G : BipGraph n) (γ : F)
    (α : Fin (n * n) → F) (hγ : OrderAtLeast γ (n * r))
    (hα : Function.Injective fun x : Fin (n * n) × Fin r => α x.1 * γ ^ (x.2 : ℕ))
    (hδ : n ≤ δ) (hr : n ^ 2 * δ < r) :
    G.HasPM ↔ (matchingMatrix γ α r (n * (r - δ)) G).rank = n * (n * (r - δ)) := by sorry

end BipMatchNC.Weighted
