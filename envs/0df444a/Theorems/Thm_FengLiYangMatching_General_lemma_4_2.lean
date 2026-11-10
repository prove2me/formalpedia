-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_4_2
-- name    : FengLiYangMatching.General.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:13.033862+00:00
-- url     : https://prove2.me/theorems/98910d51-554a-4f5a-9193-0fd1f0a2b1c1
-- title:
--   Lemma 4.2 — pathwise endpoint-addition comparison
-- statement:
--   Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. The base graph B is finite and loopless, x₁≠x₂ lie outside it, Y consists of base vertices, and the marked reference vertices are a subset of Y of size at most two. Potential added edges connect {x₁,x₂} to Y. All Greedy runs use one common order on base and potential edges; N,R,K,N₁,R₁ count matched vertices in the augmented graph, B, and C=B_e−x₂ as in the shared definitions. μ(y) is the actual probability that Greedy on B matches y.
--
--   For every fixed permutation σ of all base and potential edges, and every retained subset of the potential edges,
--
--   $$3N+2R\ge3N_1+2R_1.$$
--
--   This is a pathwise statement, including one or two marked references and also the empty marked set. It compares recovery counts when the second endpoint is restored.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - generalization: B and its added edges arise from a conditioned recovery graph → any finite loopless base graph disjoint from x₁,x₂, allowed potential edges, and a marked subset of Y of cardinality at most two, for every fixed order and retention pattern; reason: the Appendix A comparison uses only this local graph and the common order; every source recovery configuration is included, and this pathwise statement has no probability parameter
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 4.2, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_4_2 {n : ℕ} (d : Local n) (hd : d.Valid) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (σ : List (Edge n)) (hσ : σ.Perm (d.base ∪ d.potential).toList)
    (r : EdgeSet n) (hr : r ⊆ d.potential) :
    3 * N d σ r + 2 * R d σ r ≥ 3 * N1 d σ r + 2 * R1 d σ r := by sorry

end FengLiYangMatching.General
