-- Prove2me | Theorems.Thm_BipDijoin_claim_3_1
-- name    : BipDijoin.claim_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:38.158754+00:00
-- url     : https://prove2.me/theorems/24750d7e-ce7f-48c7-b84b-57b3669c59e6
-- title:
--   Claim 3.1 — contracting a strong end splits $\gamma$: $\gamma(G)=\gamma(G/U)+\gamma(G[U])$
-- statement:
--   Let $G$ be a bipartite multigraph with every edge directed from $L$ to $R$, and let $\gamma(\cdot)$ denote the minimum size of a dijoin. For every strong end $U$ of $G$ (source or sink),
--   $$\gamma(G)=\gamma(G/U)+\gamma(G[U]),$$
--   where $G/U$ contracts $U$ to a new vertex (on $L$ for a source end, on $R$ for a sink end), discarding loops and keeping parallel edges.
--
--   The claim shows that contracting a strong end preserves an optimal dijoin, which is the basis of Frank's end-decomposition framework and of the relaxed decompositions of this paper.
--
--   **Formalization Note** The new vertex is any fresh name. Edge identities survive contraction. The proof also gives $\gamma(G[U])=|U|/2$, which the claim does not state.
--
--   Differences from the source:
--   - generalization: G the 2-edge-connected graph of the paper's setting (§2.1, p.3) → every well-formed bipartite multigraph; reason: the claim uses only Definition 2.1; on 2-edge-connected graphs the Lean statement is the source's
--   - encoding: G/U with an unnamed new vertex → contraction to any vertex x ∉ V(G), on L for a source end and on R for a sink end; reason: Lean needs a name; every fresh name gives the same quotient up to renaming
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Claim 3.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsDicut
import Definitions.Def_BipDijoin_IsStrongEnd

set_option autoImplicit false

namespace BipDijoin

/-- **Claim 3.1** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.4 = PDF p.6). "For a strong end U, γ(G) = γ(G/U) + γ(G[U])."

For every well-formed bipartite multigraph `G`, every strong end `U` of `G` and every fresh vertex
`x`, contracting `U` to `x` (placed on the left for a source end, on the right for a sink end):
`γ(G) = γ(G/U) + γ(G[U])`.

**Formalization Note.** `γ` is the minimum dijoin size, a dijoin being an arc set meeting every
dicut. Edge identities survive contraction. The proof also shows `γ(G[U]) = |U|/2`, which the
claim does not state. -/
theorem claim_3_1 (G : BipGraph) (hG : G.WF) (U : Finset ℕ) (x : ℕ) (hx : x ∉ G.V) (s : Bool)
    (hU : (G.IsSourceEnd U ∧ s = true) ∨ (G.IsSinkEnd U ∧ s = false)) :
    G.gamma = (G.contract U x s).gamma + (G.induced U).gamma := by sorry

end BipDijoin
