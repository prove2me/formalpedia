-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_4_3
-- name    : FengLiYangMatching.General.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:47:58.531588+00:00
-- url     : https://prove2.me/theorems/616ff74d-bd3c-4c6e-b588-c8bb21df1b45
-- title:
--   Lemma 4.3 — single-endpoint comparison after deleting z
-- statement:
--   Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. The base graph B is finite and loopless, x₁≠x₂ lie outside it, Y consists of base vertices, and the marked reference vertices are a subset of Y of size at most two. Potential added edges connect {x₁,x₂} to Y. All Greedy runs use one common order on base and potential edges; N,R,K,N₁,R₁ count matched vertices in the augmented graph, B, and C=B_e−x₂ as in the shared definitions. μ(y) is the actual probability that Greedy on B matches y. The order is uniform and independent of Bernoulli(q) retention, with 5/8≤q≤1, whenever an expectation is taken.
--
--   Choose either endpoint x, a marked vertex y with potential edge xy, and a base vertex z≠y. Delete z and add x with its retained edges to Y\{z}, obtaining D. Fix arbitrary retention outcomes of every potential edge except xy; retain xy independently with probability q. Let n and r indicate whether x and y are matched by Greedy on D. With expectation also over the uniform common order,
--
--   $$\mathbb E[3n+2r]\ge3-\mu(y).$$
--
--   Marked labels remain counted even when incident edges are deleted. The comparison is used after another endpoint has already been matched.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - generalization: B and its added edges arise from a conditioned recovery graph → any finite loopless base graph disjoint from x₁,x₂, with arbitrary allowed potential edges and q∈[5/8,1]; reason: the source comparisons depend only on this local data, including the reduced configurations of §4.3; the original experiment has q=(1−b)/(1−s) in this interval
--   - encoding: uniform common edge order and independent retained edges → exact finite averages over all permutations and all retention subsets; reason: the permutations have equal positive weight and Bernoulli weights give precisely the independent product distribution
--   - reading: the independent reference edge is random in Lemma 4.3 and Appendix A fixes the other outcomes → arbitrary fixed outcomes for other potential edges, with only the reference coin averaged; reason: Appendix A pp. 24–25 conditions on these outcomes before proving the inequality; averaging recovers the unconditioned statement
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 4.3, p. 15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_4_3 {n : ℕ} (d : Local n) (hd : d.Valid) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1)
    (x y z : Fin n) (hx : x ∈ ({d.x1,d.x2} : Finset (Fin n)))
    (hy : y ∈ d.marked) (hz1 : z ≠ d.x1) (hz2 : z ≠ d.x2) (hzy : z ≠ y)
    (hedge : s(x,y) ∈ d.potential) (fixed : EdgeSet n)
    (hfixed : fixed ⊆ d.potential) (href : s(x,y) ∉ fixed) :
    singleMean d q s(x,y) fixed (fun σ r =>
      3 * count {x} (deletedRun d x z σ r) + 2 * count {y} (deletedRun d x z σ r))
      ≥ 3 - mu d y := by sorry

end FengLiYangMatching.General
