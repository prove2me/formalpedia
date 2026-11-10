-- Prove2me | Theorems.Thm_BipDijoin_theorem_A_1
-- name    : BipDijoin.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:58.627895+00:00
-- url     : https://prove2.me/theorems/1ef2a591-16fe-43fe-9323-5f70785df3db
-- title:
--   Theorem A.1, first two sentences — strong ends exist for maximum matchings; end decompositions exist (corrected: at least two vertices)
-- statement:
--   Let $G$ be a 2-edge-connected bipartite multigraph.
--
--   1. If $G$ has at least two vertices, then for every maximum matching $M$ of $G$ there is a set $U$ with $|U|\ge2$ that is a source or a sink SCC of $G_M$ and is fitted by $M$; by Definition 2.1, $U$ is a strong end fitted by $M$.
--   2. $G$ has a bipartite end decomposition in which every recorded matching is maximum (Definition 2.2).
--
--   This is Frank's strong-end theorem in its bipartite form; it guarantees that Frank's algorithm, which always repairs a maximum matching, never gets stuck.
--
--   **Formalization Note** The third and fourth sentences of Theorem A.1 (independence of the number of end-reductions, Frank's $O(mn)$ time) are not posed.
--
--   Differences from the source:
--   - correction: for every 2-edge-connected bipartite multigraph G and maximum matching M there is a strong end fitted by M → the first clause assumes |V(G)| ≥ 2; reason: the one-vertex graph is 2-edge-connected (the paper's own convention: the proof of Theorem 4.2 calls it already terminal) and has no strong end
--   - encoding: a strong end U such that M fits U → a set U with |U| ≥ 2 that is a source or sink SCC of G_M and is fitted by M; reason: Definition 2.1: such a U is a strong end; this is the form Frank's algorithm uses (step 3, p.45)
--   - encoding: an end decomposition with unnamed contracted vertices → representatives named N₀, N₀ + 1, … for any N₀ above every vertex name; reason: Lean needs names; any fresh names give the same decomposition up to renaming
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Theorem A.1, p.44 (PDF p.46)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd
import Definitions.Def_BipDijoin_IsPartialDecomp

set_option autoImplicit false

namespace BipDijoin

/-- **Theorem A.1**, first two sentences (Nalam–Saranurak, STOC 2027 submission (manuscript
sha256 382f85e4…7fea6), p.44 = PDF p.46; [Fra93]). "Given a 2-edge-connected bipartite multigraph G
and any maximum matching M of G, there exists a strong end U such that M fits U. Consequently, G
has a bipartite end-decomposition and a fitting sequence of maximum matchings."

For every well-formed 2-edge-connected bipartite multigraph `G`:
1. if `G` has at least two vertices, then for every maximum matching `M` there is a set `U` with
   `|U| ≥ 2` that is a source or a sink SCC of `G_M` (hence a strong end) and that `M` fits;
2. for every `N₀` above all vertex ids, `G` has a bipartite end decomposition (Definition 2.2,
   every `Mⁱ` maximum) with representatives `N₀, N₀ + 1, …`.

**Formalization Note.** Correction: a one-vertex graph is 2-edge-connected (the paper's own
convention: the proof of Theorem 4.2 calls it "already terminal") and has no strong end, so
clause 1 needs `|V(G)| ≥ 2`. Clause 2 holds as printed (the empty decomposition). -/
theorem theorem_A_1 (G : BipGraph) (hG : G.WF) (h2 : G.TwoEdgeConnected) :
    (2 ≤ G.V.card → ∀ M, G.IsMaxMatching M →
      ∃ U : Finset ℕ, 2 ≤ U.card ∧
        (IsSourceSCC (G.altArc M) G.V U ∨ IsSinkSCC (G.altArc M) G.V U) ∧ G.Fits M U) ∧
    (∀ N₀ : ℕ, (∀ v ∈ G.V, v < N₀) → ∃ recs, IsDecomp true G N₀ recs) := by sorry

end BipDijoin
