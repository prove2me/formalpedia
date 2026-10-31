-- Prove2me | Theorems.Thm_ChenPairedDomination_Interval_lemma_9
-- name    : ChenPairedDomination.Interval.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-31T01:26:51.493265+00:00
-- url     : https://prove2.me/theorems/6c3e0717-f6ff-46ff-8cd9-4ff6724016be
-- title:
--   Lemma 9 — the three-case minimum-set recurrence
-- statement:
--   Let G be a connected finite simple interval graph in its supplied left-endpoint order. Suppose F(u_i)=u_k and F(u_k)=u_j, where j < k < i. Write w(u_j) for the last earlier nonneighbor, using the external sentinel u_0 when none exists. All three conclusions hold:
--
--   1. If w(u_j)=u_l with l ≥ 2, then for every minimum paired-dominating set S_l of G[V_l], the exact set S_l ∪ {u_j,u_k} is a minimum paired-dominating set of G[V_i].
--   2. If w(u_j)=u_1, then {u_1,u_2,u_j,u_k} is a minimum paired-dominating set of G[V_i].
--   3. If w(u_j)=u_0, then {u_j,u_k} is a minimum paired-dominating set of G[V_i].
--
--   The statement retains feasibility as well as minimum cardinality for each displayed construction. The strict index chain ensures that the first two vertices exist.
--
--   Differences from the source:
--   - encoding: vertices u_1,...,u_n and prefixes V_r → vertices Fin n, with u_i at index i-1 and prefixVertices r containing indices below r; reason: this is the same finite ordered enumeration
--   - encoding: an interval representation ordered by increasing left endpoints → nonempty closed real intervals with nondecreasing left endpoints, permitting ties and point intervals; reason: this makes the endpoint convention explicit without restricting lengths or the real endpoint domain
--   - encoding: a minimum paired-dominating set of an induced prefix → a finite subset that dominates that prefix, has a perfect matching on its own induced carrier, and is no larger than any feasible competitor; reason: this makes feasibility and minimum cardinality explicit without choosing a distinguished optimizer
--   - encoding: external sentinel u_0 and case l ≥ 2 → Option.none distinct from actual index 0, and 1 ≤ l.val; reason: the vertex indices shift by one while the sentinel remains outside the vertex type
--   - reading: PD_i = PD_l ∪ {u_j,u_k}, or the displayed base sets → every optimum S_l gives the displayed optimal union, and each displayed base set is optimal; reason: PD denotes an attainable optimum, not a unique choice function; the proof checks these constructed sets and their size
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, Lemma 9, p. 12

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

namespace ChenPairedDomination.Interval

theorem lemma_9
    {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (i j k : Fin n) (hjk : j < k) (hki : k < i)
    (hFk : firstNeighbor G i = k) (hFj : firstNeighbor G k = j) :
    (∀ l : Fin n, 1 ≤ l.val → lastNonneighbor G j = some l →
      ∀ S : Finset (Fin n), MinimumPairedDominatesOn G (prefixVertices (l.val + 1)) S →
        MinimumPairedDominatesOn G (prefixVertices (i.val + 1)) (S ∪ {j, k})) ∧
    (lastNonneighbor G j = some ⟨0, by omega⟩ →
      MinimumPairedDominatesOn G (prefixVertices (i.val + 1))
        {⟨0, by omega⟩, ⟨1, by omega⟩, j, k}) ∧
    (lastNonneighbor G j = none →
      MinimumPairedDominatesOn G (prefixVertices (i.val + 1)) {j, k}) := by sorry

end ChenPairedDomination.Interval
