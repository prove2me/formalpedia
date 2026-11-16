-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_Supplement_lemma_8_4
-- name    : DistributedMWC440.UpperBound.Supplement.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:22.422201+00:00
-- url     : https://prove2.me/theorems/05bea025-0641-4c57-b7db-8b7e6e625b52
-- title:
--   Lemma 8.4 (Approximation gap in the CONGEST construction)
-- statement:
--   Let $k\ge1$, $d\ge2$ and $p\ge1$ be integers and let $H=(L\cup R,E_H)$ be a bipartite graph with parts of equal size $\gamma$ and girth greater than $2k$. For all $x,y\in\{0,1\}^{E_H}$ the graph $G_{d,p}(H,x,y)$ satisfies the following.
--
--   1. Directed unweighted variant: if $\langle x,y\rangle\neq0$ then $\mathrm{OPT}\le2d^p$; if $\langle x,y\rangle=0$ then $\mathrm{OPT}\ge2(k+1)d^p$.
--   2. Undirected weighted variant (edges from $H$ weight $1$, path edges $0$, overlay edges $2(k+1)$): if $\langle x,y\rangle\neq0$ then $\mathrm{OPT}\le2$; if $\langle x,y\rangle=0$ then $\mathrm{OPT}\ge2(k+1)$.
--
--   $\mathrm{OPT}$ is $\infty$ when there is no cycle. The long paths and the overlay tree keep the gap of Lemma 8.1 while making the diameter $O(p)$; the lemma is the gap step of the CONGEST lower bound (Theorem 2, via Proposition 8.8).
--
--   Differences from the source:
--   - encoding: bipartite H = (L ∪ R, E_H) with |L| = |R| = γ and x, y ∈ {0,1}^{E_H} → an edge set E ⊆ Fin γ × Fin γ of the bipartite graph on Fin γ ⊕ Fin γ and Boolean functions x, y on E; reason: the same objects
--   - encoding: girth(H) > 2k → (2k : ℕ∞) < egirth of H (∞ for a forest); reason: Mathlib's extended girth; a forest has no cycle and satisfies the source's hypothesis
--   - encoding: OPT, the minimum cycle weight → the extended infimum over simple cycles (base `optimum`; least number of arcs for digraphs), equal to ∞ when there is no cycle; reason: the lower bounds OPT ≥ … then also cover acyclic graphs, as the source's 'every cycle has weight at least' does
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), Lemma 8.4, printed p. 47 / PDF p. 49; construction printed pp. 46–47 / PDF pp. 48–49.

import Definitions.Def_DistributedMWC440_UpperBound_Supplement_Gadgets

open scoped ENNReal
noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-- Lemma 8.4 (Approximation gap in the CONGEST construction), Chang et al., STOC 2027
submission #440, printed p. 47 / PDF p. 49 (construction printed pp. 46–47 / PDF pp. 48–49).
For an integer `k ≥ 1`, integers `d ≥ 2`, `p ≥ 1`, a bipartite `H` with parts `Fin γ`, `Fin γ`,
edge set `E` and girth greater than `2k`, and all `x, y`: in the directed unweighted variant of
`G_{d,p}(H, x, y)`, `OPT ≤ 2d^p` if `⟨x,y⟩ ≠ 0` and `OPT ≥ 2(k+1)d^p` if `⟨x,y⟩ = 0`; in the
undirected weighted variant, `OPT ≤ 2` resp. `OPT ≥ 2(k+1)`. -/
theorem lemma_8_4 (k : ℕ) (hk : 1 ≤ k) (γ d p : ℕ) (hd : 2 ≤ d) (hp : 1 ≤ p)
    (E : Finset (Fin γ × Fin γ)) (hgirth : ((2 * k : ℕ) : ℕ∞) < (HGraph γ E).egirth)
    (x y : E → Bool) :
    (inner E x y ≠ 0 → dOptimum (congDigraph d p E x y) ≤ 2 * ((d : ℝ≥0∞) ^ p)) ∧
    (inner E x y = 0 →
      2 * ((k : ℝ≥0∞) + 1) * (d : ℝ≥0∞) ^ p ≤ dOptimum (congDigraph d p E x y)) ∧
    (inner E x y ≠ 0 → optimum (congWGraph k d p E x y) ≤ 2) ∧
    (inner E x y = 0 → 2 * ((k : ℝ≥0∞) + 1) ≤ optimum (congWGraph k d p E x y)) := by sorry

end DistributedMWC440.UpperBound.Supplement
