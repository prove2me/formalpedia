-- Prove2me | Theorems.Thm_ChenPairedDomination_Interval_lemma_8
-- name    : ChenPairedDomination.Interval.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-31T01:27:09.658468+00:00
-- url     : https://prove2.me/theorems/f4e62b1e-4800-445e-9256-961848b16dbb
-- title:
--   Lemma 8 — monotonicity of prefix optimum
-- statement:
--   Let G be a connected finite simple interval graph in its supplied left-endpoint order. For 2 ≤ r ≤ n−1, let S and T be any minimum paired-dominating sets of G[V_r] and G[V_{r+1}], respectively. Then
--
--   $$|S|\le |T|.$$
--
--   Both minimum-set witnesses are explicit. No optimum is taken on a singleton or empty prefix.
--
--   Differences from the source:
--   - encoding: vertices u_1,...,u_n and prefixes V_r → vertices Fin n, with u_i at index i-1 and prefixVertices r containing indices below r; reason: this is the same finite ordered enumeration
--   - encoding: an interval representation ordered by increasing left endpoints → nonempty closed real intervals with nondecreasing left endpoints, permitting ties and point intervals; reason: this makes the endpoint convention explicit without restricting lengths or the real endpoint domain
--   - encoding: a minimum paired-dominating set of an induced prefix → a finite subset that dominates that prefix, has a perfect matching on its own induced carrier, and is no larger than any feasible competitor; reason: this makes feasibility and minimum cardinality explicit without choosing a distinguished optimizer
--   - encoding: 2 ≤ i ≤ n−1 → 2 ≤ r and r+1 ≤ n; reason: equivalent natural-number bounds avoid truncated subtraction
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, Lemma 8, p. 11

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

open ChenPairedDomination.Interval

namespace ChenPairedDomination.Interval

theorem lemma_8
    {n : ℕ} (G : SimpleGraph (Fin n)) (R : OrderedRepresentation G)
    (hconn : G.Connected) (r : ℕ) (hr : 2 ≤ r) (hrn : r + 1 ≤ n)
    (S T : Finset (Fin n))
    (hS : MinimumPairedDominatesOn G (prefixVertices r) S)
    (hT : MinimumPairedDominatesOn G (prefixVertices (r + 1)) T) :
    S.card ≤ T.card := by sorry

end ChenPairedDomination.Interval
