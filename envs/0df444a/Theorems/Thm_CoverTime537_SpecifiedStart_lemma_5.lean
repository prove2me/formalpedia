-- Prove2me | Theorems.Thm_CoverTime537_SpecifiedStart_lemma_5
-- name    : CoverTime537.SpecifiedStart.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:19.418574+00:00
-- url     : https://prove2.me/theorems/27de6914-fd90-4f53-b7a4-4291cbbc92d3
-- title:
--   Lemma 5 — cover times and the last vertex discovered
-- statement:
--   Let $H$ be any finite connected simple undirected graph with at least two vertices. For each vertex $x$, let $C_H(x)$ be the expected full cover time for the ordinary uniform-neighbor walk, with its initial vertex discovered at time zero. For every vertex $v$,
--
--   $$\deg_H(v)+\sum_{y\sim v}C_H(y)-\deg_H(v)C_H(v)=\sum_x\deg_H(x)\mathbb P_x(v\text{ is the last vertex discovered}).$$
--
--   This identity applies without a hub, degree, planarity or bipartiteness restriction. It supplies the general residual identity used at the hub.
--
--   Differences from the source:
--   - encoding: walk expectation and event probabilities → finite trajectory cylinder probabilities and real tail sums; reason: time zero and all ordinary walk instances are preserved; convergence is a separate supporting target, never an added premise
-- source:
--   Ryan Aghazadeh, STOC 2027 submission #537 (October 2026), Lemma 5 p.7 (6)

import Definitions.Def_CoverTime537_SpecifiedStart_Walk

namespace CoverTime537.SpecifiedStart
open scoped BigOperators
/-- Aghazadeh, STOC 2027 submission #537, Lemma 5, p.7, (6).
All finite connected simple undirected graphs with at least two vertices. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hc : H.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    (H.degree v : ℝ) + (∑ y ∈ H.neighborFinset v, cover H y) -
      (H.degree v : ℝ) * cover H v =
        ∑ x : V, (H.degree x : ℝ) * lastProb H x v := by sorry
end CoverTime537.SpecifiedStart
