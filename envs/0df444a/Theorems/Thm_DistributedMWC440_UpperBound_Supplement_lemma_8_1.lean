-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_Supplement_lemma_8_1
-- name    : DistributedMWC440.UpperBound.Supplement.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:50:39.528442+00:00
-- url     : https://prove2.me/theorems/ade61b50-eb0e-4d01-b7e8-93d30efab3cb
-- title:
--   Lemma 8.1 (Approximation gap in the basic construction)
-- statement:
--   Let $k\ge1$ be an integer and let $H=(L\cup R,E_H)$ be a bipartite graph with parts of equal size $\gamma$ and girth greater than $2k$. For all $x,y\in\{0,1\}^{E_H}$ the basic two-copy graph $G(H,x,y)$ satisfies the following.
--
--   1. Directed unweighted variant: if $\langle x,y\rangle\neq0$ then $\mathrm{OPT}\le4$; if $\langle x,y\rangle=0$ then $\mathrm{OPT}\ge4(k+1)$.
--   2. Undirected weighted variant (matching edges of weight $0$, copy edges of weight $1$): if $\langle x,y\rangle\neq0$ then $\mathrm{OPT}\le2$; if $\langle x,y\rangle=0$ then $\mathrm{OPT}\ge2(k+1)$.
--
--   Here $\mathrm{OPT}$ is the minimum weight of a (directed, resp. undirected simple) cycle, $\infty$ if there is none. The factor $k+1$ between the two cases is the approximation gap that turns set-disjointness into $(k+1-\varepsilon)$-Apx-MWC; the lemma is used for the broadcast congested clique lower bound (Theorem 5, via Proposition 8.2) and, through Lemma 8.4, for the CONGEST lower bound (Theorem 2).
--
--   Differences from the source:
--   - encoding: bipartite H = (L ∪ R, E_H) with |L| = |R| = γ and x, y ∈ {0,1}^{E_H} → an edge set E ⊆ Fin γ × Fin γ of the bipartite graph on Fin γ ⊕ Fin γ and Boolean functions x, y on E; reason: the same objects
--   - encoding: girth(H) > 2k → (2k : ℕ∞) < egirth of H (∞ for a forest); reason: Mathlib's extended girth; a forest has no cycle and satisfies the source's hypothesis
--   - encoding: OPT, the minimum cycle weight → the extended infimum over simple cycles (base `optimum`; least number of arcs for digraphs), equal to ∞ when there is no cycle; reason: the lower bounds OPT ≥ … then also cover acyclic graphs, as the source's 'every cycle has weight at least' does
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), Lemma 8.1, printed p. 44 / PDF p. 46; construction printed pp. 43–44 / PDF pp. 45–46.

import Definitions.Def_DistributedMWC440_UpperBound_Supplement_Gadgets

open scoped ENNReal
noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-- Lemma 8.1 (Approximation gap in the basic construction), Chang et al., STOC 2027 submission
#440, printed p. 44 / PDF p. 46. For an integer `k ≥ 1` and a bipartite `H` with parts
`Fin γ`, `Fin γ`, edge set `E` and girth greater than `2k`, and all `x, y ∈ {0,1}^{E_H}`:
in the directed unweighted variant of `G(H, x, y)`, `OPT ≤ 4` if `⟨x,y⟩ ≠ 0` and
`OPT ≥ 4(k+1)` if `⟨x,y⟩ = 0`; in the undirected weighted variant, `OPT ≤ 2` resp.
`OPT ≥ 2(k+1)`. `OPT` is `⊤` when there is no cycle. -/
theorem lemma_8_1 (k : ℕ) (hk : 1 ≤ k) (γ : ℕ) (E : Finset (Fin γ × Fin γ))
    (hgirth : ((2 * k : ℕ) : ℕ∞) < (HGraph γ E).egirth) (x y : E → Bool) :
    (inner E x y ≠ 0 → dOptimum (basicDigraph E x y) ≤ 4) ∧
    (inner E x y = 0 → 4 * ((k : ℝ≥0∞) + 1) ≤ dOptimum (basicDigraph E x y)) ∧
    (inner E x y ≠ 0 → optimum (basicWGraph E x y) ≤ 2) ∧
    (inner E x y = 0 → 2 * ((k : ℝ≥0∞) + 1) ≤ optimum (basicWGraph E x y)) := by sorry

end DistributedMWC440.UpperBound.Supplement
