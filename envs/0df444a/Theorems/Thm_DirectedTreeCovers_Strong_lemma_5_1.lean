-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_lemma_5_1
-- name    : DirectedTreeCovers.Strong.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:29:35.375927+00:00
-- url     : https://prove2.me/theorems/c63f56dc-dc33-4a0a-8af2-35856eb74c50
-- title:
--   Lemma 5.1 — strong stretch of Algorithm 3
-- statement:
--   Let $G=(V,E,\omega)$ be a finite strongly connected directed graph with nonnegative real edge weights, let $k\ge1$, and fix an outcome of the nested hierarchy. The collection $\mathcal T$ computed by Algorithm 3 consists of valid incoming/outgoing shortest-path tree-pairs. Simultaneously for every ordered pair $u,v\in V$, some $ET\in\mathcal T$ satisfies
--
--   $$d_{ET}(u,v)\le d_G(u,v)+(k-1)r_G(u,v).$$
--
--   The pair is chosen from the same computed collection for every query; no stretch invariant is assumed. This is the exact stretch half of the main theorem, with coefficient $k-1$, and preserves actual directed paths.
--
--   Differences from the source:
--   - generalization: finite directed graphs → finite directed multigraphs, allowing parallel edges and loops; reason: simple directed graphs embed by their edge identities; finite nonnegative shortest walks still exist
--   - generalization: the nonempty strongly connected construction setting → also the empty graph and every coin array, including null outcomes; reason: empty conclusions are vacuous; every coin array determines a nested hierarchy and the stretch argument is deterministic
--   - reading: searches rooted in a possibly empty expanded cluster → missing-root searches return empty slots, omitted from the pair collection; reason: zero radii can exclude the root; no path is lost by omitting a search with no reachable vertex
--   - encoding: incoming and outgoing shortest-path searches with fixed ties → tight parent edges with decreasing minimum shortest-walk hop count and a fixed finite-set selector; reason: this selects genuine shortest-path trees and prevents zero-weight cycles without restricting weights
--   - encoding: extended shortest-walk distances and the strong-stretch inequality → ENNReal distances and k*d(u,v)+(k-1)*d(v,u), with 0*infinity=0; reason: the source displays this equivalent form in Section 2; k>=1 makes natural subtraction exact
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, Lemma 5.1, printed p.17 (PDF p.18), proof continues printed p.18 (PDF p.19); Section 2 standing assumptions printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Construction

namespace DirectedTreeCovers.Strong

/-- Lemma 5.1, Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840
(October 2026), printed p.17 / PDF p.18; proof continues printed p.18 / PDF p.19.
This is the computed Algorithm 3 collection, including genuine tree validity,
and not a hypothesis asserting that an arbitrary execution already succeeds.
Empty search slots are omitted. The empty input is also admitted. -/
theorem lemma_5_1 {V E : Type} [Fintype V] [Fintype E]
    (G : EulerSparsify.DiGraph V E) (hG : Nonnegative G) (hsc : StronglyConnected G)
    (k : ℕ) (hk : 1 ≤ k) (ω : Coins V k) :
    StrongCover G k (algorithmCover G k ω) := by sorry

end DirectedTreeCovers.Strong
