-- Prove2me | Theorems.Thm_ChenPairedDomination_Interval_observation_6
-- name    : ChenPairedDomination.Interval.observation_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-31T01:27:13.657775+00:00
-- url     : https://prove2.me/theorems/0ead8d17-5280-4a98-946f-d5234895264a
-- title:
--   Observation 6 — connected prefixes
-- statement:
--   Let G be a connected finite simple interval graph with a supplied closed real interval representation ordered by nondecreasing left endpoints. For every r with 1 ≤ r ≤ n,
--
--   $$G[V_r] \text{ is connected},\qquad V_r=\{u_1,\ldots,u_r\}.$$
--
--   The conclusion includes the singleton prefix. It does not assert that the singleton prefix has a paired-dominating set.
--
--   Differences from the source:
--   - encoding: vertices u_1,...,u_n and prefixes V_r → vertices Fin n, with u_i at index i-1 and prefixVertices r containing indices below r; reason: this is the same finite ordered enumeration
--   - encoding: an interval representation ordered by increasing left endpoints → nonempty closed real intervals with nondecreasing left endpoints, permitting ties and point intervals; reason: this makes the endpoint convention explicit without restricting lengths or the real endpoint domain
--   - generalization: the standing graph convention excludes isolated vertices → the original connected graph may also be a singleton; reason: its only nonempty prefix is itself and is connected, while all source graphs are still included
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, Observation 6, p. 11

import Definitions.Def_ChenPairedDomination_Interval_PrefixData

namespace ChenPairedDomination.Interval

theorem observation_6
    {n : ℕ} (G : SimpleGraph (Fin n))
    (R : ChenPairedDomination.Interval.OrderedRepresentation G) (hconn : G.Connected)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (G.induce (↑(ChenPairedDomination.Interval.prefixVertices (n := n) r) : Set (Fin n))).Connected := by sorry

end ChenPairedDomination.Interval
