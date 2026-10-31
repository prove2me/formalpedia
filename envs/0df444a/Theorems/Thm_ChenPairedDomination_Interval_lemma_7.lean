-- Prove2me | Theorems.Thm_ChenPairedDomination_Interval_lemma_7
-- name    : ChenPairedDomination.Interval.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-31T01:27:04.879665+00:00
-- url     : https://prove2.me/theorems/492b93cd-24c6-4cad-b46b-df6b7ef381c1
-- title:
--   Lemma 7 — the two-vertex base case
-- statement:
--   Let G be a connected finite simple interval graph with its supplied left-endpoint order, and let F(u_i) be the least earlier neighbor, with F(u_1)=u_1. If F(u_i) differs from u_i and F(F(u_i))=F(u_i), then
--
--   $$\{u_i,F(u_i)\} \text{ is a minimum paired-dominating set of } G[V_i].$$
--
--   In particular the exact displayed set is feasible and has minimum cardinality over all paired-dominating sets of the prefix. The antecedent excludes the singleton case.
--
--   Differences from the source:
--   - encoding: vertices u_1,...,u_n and prefixes V_r → vertices Fin n, with u_i at index i-1 and prefixVertices r containing indices below r; reason: this is the same finite ordered enumeration
--   - encoding: an interval representation ordered by increasing left endpoints → nonempty closed real intervals with nondecreasing left endpoints, permitting ties and point intervals; reason: this makes the endpoint convention explicit without restricting lengths or the real endpoint domain
--   - encoding: a minimum paired-dominating set of an induced prefix → a finite subset that dominates that prefix, has a perfect matching on its own induced carrier, and is no larger than any feasible competitor; reason: this makes feasibility and minimum cardinality explicit without choosing a distinguished optimizer
--   - reading: PD_i denotes a minimum paired-dominating set and PD_i = {u_i,F(u_i)} → the exact displayed pair is a minimum paired-dominating set; reason: the source proof verifies the pair’s feasibility and optimality; it does not assert uniqueness of all optimizers
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, Lemma 7, p. 11

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

namespace ChenPairedDomination.Interval

theorem lemma_7
    {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (i : Fin n)
    (hF : firstNeighbor G i ≠ i)
    (hFF : firstNeighbor G (firstNeighbor G i) = firstNeighbor G i) :
    MinimumPairedDominatesOn G (prefixVertices (i.val + 1)) {i, firstNeighbor G i} := by sorry

end ChenPairedDomination.Interval
