-- Prove2me | Theorems.Thm_CycleLengthsExp_BetaGraph_cycle_of_copy
-- name    : CycleLengthsExp.BetaGraph.cycle_of_copy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:25.675722+00:00
-- url     : https://prove2.me/theorems/6f3be146-96fa-4e3b-aa81-b5d42ad36191
-- title:
--   p. 16 — a β-graph containing a copy of T_{k,t,ℓ−2t−1} with k ≥ 2 and t ≥ log_k(βn) has a cycle of length ℓ
-- statement:
--   Let $\beta>0$ and let $G$ be a β-graph on $n$ vertices. Let $k,t,p$ be positive integers with $k\ge 2$ and $t\ge\log_k(\beta n)$, that is $k^t\ge\beta n$. If $G$ contains a copy of $T_{k,t,p}$, then $G$ contains a cycle of length
--   $$\ell = 2t+1+p .$$
--
--   The reason is that each of the two $k$-ary trees has $k^t\ge\beta n$ leaves, so the β-graph property gives an edge between the two leaf sets, and that edge closes a cycle through both roots. This is how embedded trees are turned into cycles of every length in the proof of Theorem 3.
--
--   **Formalization Note** The paper writes the tree as $T_{k,t,\ell-2t-1}$; here the path length $p$ is the parameter and $\ell=2t+1+p$, avoiding natural-number subtraction. The condition $t\ge\log_k(\beta n)$ is stated as $\beta n\le k^t$, which is equivalent for $\beta n>0$. "Contains a copy" is `SimpleGraph.IsContained`.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 16, proof of Theorem 3, first paragraph ("Observe that if G contains a copy of T_{k,t,ℓ−2t−1} …")

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

namespace CycleLengthsExp.BetaGraph

/-- The cycle-closing observation (p. 16): if a β-graph `G` on `n` vertices contains a copy of
`T_{k,t,p}` with `k ≥ 2` and `t ≥ log_k(βn)` (i.e. `βn ≤ k^t`), then `G` contains a cycle of
length `ℓ = 2t + 1 + p` (the page writes `p = ℓ - 2t - 1`). -/
theorem cycle_of_copy (β : ℝ) (hβ : 0 < β) (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : IsBetaGraph β G) (k t p : ℕ) (hk : 2 ≤ k) (ht : 0 < t) (hp : 0 < p)
    (hkt : β * n ≤ (k : ℝ) ^ t) (hT : (Tktp k t p).IsContained G) :
    2 * t + 1 + p ∈ CycleLengthsExp.WellSpread.cycleLengths G := by sorry

end CycleLengthsExp.BetaGraph
