-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_lemma_3_7
-- name    : BipMatchNC.Weighted.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:13:21.534418+00:00
-- url     : https://prove2.me/theorems/9b6eb850-33c4-4b87-adb3-4a6aeded9c4a
-- title:
--   Lemma 3.7: a balanced bipartite graph with a perfect matching has an optimal dual of value w* with y ≤ 0 ≤ z and all |values| ≤ 2nW
-- statement:
--   Let $G$ be a balanced bipartite graph on $[n]+[n]$ with edge weights $w:E\to\mathbb N$ that has a perfect matching, let $w^*$ be the maximum weight of a perfect matching and $W$ the maximum weight of an edge. Then there is a dual solution $(y,z)$, $y,z:[n]\to\mathbb R$, which is feasible ($y_{u}+z_{v}\ge w(u,v)$ on every edge), optimal (no feasible dual has smaller value), of value
--   $$\sum_{u\in L}y_u+\sum_{v\in R}z_v=w^*,$$
--   with $y\le0$, $z\ge0$, and $|y_u|\le2nW$, $|z_v|\le2nW$ for all vertices.
--
--   The signs make the lifted dual on the blow-up graph feasible (the additional vertices receive $-y\ge0$), and the bound $2nW$ is what produces the error term $4n^3\delta W$ in Lemma 3.9.
--
--   Differences from the source:
--   - reading: w* the weight of a maximum matching in a balanced bipartite graph → w* = G.maxPMWeight w, the maximum weight of a perfect matching, with hypothesis G.HasPM; reason: w* is so defined on p. 14 and the proof starts from a maximum weight perfect matching; a maximum weight non-perfect matching can be heavier than every perfect one, and then no optimal dual has value equal to it
--   - reading: an optimal dual solution (y, z) with objective value w* → y, z with IsBalancedDualFeasible, value ≤ that of every IsBalancedDualFeasible dual, and dualValue y z = w*; reason: optimal among the duals of the balanced graph (z free, p. 15); as z ≥ 0 is also asserted, (y, z) is feasible and optimal for the printed LP too
--   - reading: the absolute values of all the dual values is bounded by 2nW → |y i| ≤ 2nW and |z j| ≤ 2nW for all i, j; reason: 'bounded by' read as ≤; the proof gives the open interval (−2nW, 2nW), which is stronger only when W > 0
--   - encoding: vertices u_1, …, u_n, v_1, …, v_n and column blocks 1, …, n² (1-based) → Fin n and Fin (n * n), 0-based; G as its bi-adjacency matrix BipGraph n; reason: indexing convention only
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 15 (PDF 16), Lemma 3.7

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Bipartite
import Definitions.Def_BipMatchNC_Weighted_Graph

namespace BipMatchNC.Weighted

theorem lemma_3_7 (n : ℕ) (G : BipGraph n) (w : Fin n → Fin n → ℕ) (hPM : G.HasPM) :
    ∃ y z : Fin n → ℝ,
      IsBalancedDualFeasible G.adj w y z ∧
      (∀ (y' z' : Fin n → ℝ), IsBalancedDualFeasible G.adj w y' z' →
        dualValue y z ≤ dualValue y' z') ∧
      dualValue y z = (G.maxPMWeight w : ℝ) ∧
      (∀ i, y i ≤ 0) ∧ (∀ j, 0 ≤ z j) ∧
      (∀ i, |y i| ≤ 2 * n * (G.maxEdgeWeight w : ℝ)) ∧
      (∀ j, |z j| ≤ 2 * n * (G.maxEdgeWeight w : ℝ)) := by sorry

end BipMatchNC.Weighted
