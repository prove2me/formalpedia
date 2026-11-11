-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_claim_4_1_1
-- name    : DirectedTreeCovers.Strong.claim_4_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:46.086629+00:00
-- url     : https://prove2.me/theorems/a26b9851-1c40-4c73-b1fb-15479284ed10
-- title:
--   Claim 4.1.1 — nested strict clusters
-- statement:
--   Let $G$ be a finite directed graph with nonnegative real edge weights, and let $R,S:V\to[0,\infty]$ satisfy $R(v)\le S(v)$ for every vertex. For every root $w$,
--
--   $$S(w,R)\subseteq S(w,S).$$
--
--   Here both clusters are obtained by the actual repeated induced-distance pruning. Specializing to two successive constructed radius functions gives Claim 4.1.1. The result supplies the cluster containment used in the strong-cover construction and overlap estimate.
--
--   Differences from the source:
--   - generalization: finite directed graphs → finite directed multigraphs, allowing parallel edges and loops; reason: simple directed graphs embed by their edge identities; finite nonnegative shortest walks still exist
--   - generalization: successive constructed radii R_i and R_(i+1) in the strongly connected setup → arbitrary pointwise ordered radius functions, without connectivity; reason: constructed successive radii are pointwise ordered and therefore specialize to this statement
--   - encoding: repeatedly remove a violating vertex until none remains → a fixed selector and |V| deletion attempts, with stationary attempts thereafter; reason: each nonstationary attempt removes one vertex, so the final set is the stated pruning output
--   - encoding: nonnegative radii and unreachable-distance infinity → ENNReal radii and directed walk infima; reason: this preserves zero and infinity without empty real-infimum defaults
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, Claim 4.1.1, printed p.14 (PDF p.15); proof printed p.15 (PDF p.16)

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Clusters

namespace DirectedTreeCovers.Strong

/-- Claim 4.1.1, Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840
(October 2026), printed p.14 / PDF p.15; proof printed p.15 / PDF p.16.
Generalized to pointwise ordered radius functions, specializing to the constructed sequence. -/
theorem claim_4_1_1 {V E : Type} [Fintype V] [Fintype E]
    (G : EulerSparsify.DiGraph V E) (hG : Nonnegative G)
    (R S : V → ENNReal) (hRS : ∀ v, R v ≤ S v) (w : V) :
    strictCluster G R w ⊆ strictCluster G S w := by sorry

end DirectedTreeCovers.Strong
