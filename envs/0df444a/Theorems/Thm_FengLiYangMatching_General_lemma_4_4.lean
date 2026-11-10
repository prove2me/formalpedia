-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_4_4
-- name    : FengLiYangMatching.General.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:22.81642+00:00
-- url     : https://prove2.me/theorems/6e86d84c-0845-4b3c-82db-485e2e490e5c
-- title:
--   Lemma 4.4 — one surviving reference-edge comparison
-- statement:
--   Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. The base graph B is finite and loopless, x₁≠x₂ lie outside it, Y consists of base vertices, and the marked reference vertices are a subset of Y of size at most two. Potential added edges connect {x₁,x₂} to Y. All Greedy runs use one common order on base and potential edges; N,R,K,N₁,R₁ count matched vertices in the augmented graph, B, and C=B_e−x₂ as in the shared definitions. μ(y) is the actual probability that Greedy on B matches y. The order is uniform and independent of Bernoulli(q) retention, with 5/8≤q≤1, whenever an expectation is taken.
--
--   Fix any retained subset of the potential edges to unmarked vertices, with all other such edges omitted. Keep independent Bernoulli(q) retention for every potential edge to a marked vertex, independent of the common uniform order. The expectation below averages this remaining randomness for each fixed nonreference pattern.
--
--   Suppose the marked set is exactly two distinct vertices y_i,y_j, and at least one edge from {x₁,x₂} to y_i exists before retention. No edge to y_j is required. Then
--
--   $$\mathbb E[3N+2R+K]\ge3+\mu(y_j).$$
--
--   This is the reduced configuration comparison after a first reference edge has been deleted. The displayed inequality is Eq. (12).
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - generalization: B and its added edges arise from a conditioned recovery graph → any finite loopless base graph disjoint from x₁,x₂, with arbitrary allowed potential edges and q∈[5/8,1]; reason: the source comparisons depend only on this local data, including the reduced configurations of §4.3; the original experiment has q=(1−b)/(1−s) in this interval
--   - encoding: uniform common edge order and independent retained edges → exact finite averages over all permutations and all retention subsets; reason: the permutations have equal positive weight and Bernoulli weights give precisely the independent product distribution
--   - reading: a surviving edge to y_i in the reduced configuration → no original pair of reference edges is assumed to survive; reason: §4.3 deletes a first edge and applies this lemma to the remaining graph; marked vertices are retained as labels
--   - reading: §4.3 fixes the nonreference retention choices before the first-edge induction → the inequality holds for every fixed nonreference retention pattern, averaging only the marked-edge coins and uniform order; reason: the source applies the lemma under that conditioning; averaging over the fixed patterns also recovers the original unconditioned experiment
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 4.4, p. 15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_4_4 {n : ℕ} (d : Local n) (hd : d.Valid) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (fixed : EdgeSet n) (hfixed : fixed ⊆ d.potential)
    (hmarked : Disjoint fixed (markedPotential d))
    (q : ℝ) (hq : 5/8 ≤ q) (hq1 : q ≤ 1)
    (yi yj : Fin n) (hne : yi ≠ yj) (hmarks : d.marked = {yi,yj})
    (hedge : ∃ x ∈ ({d.x1,d.x2} : Finset (Fin n)), s(x,yi) ∈ d.potential) :
    markedMean d q fixed (fun σ r => 3 * N d σ r + 2 * R d σ r + K d σ) ≥ 3 + mu d yj := by sorry

end FengLiYangMatching.General
