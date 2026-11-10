-- Prove2me | Theorems.Thm_BipDijoin_claim_5_7
-- name    : BipDijoin.claim_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:17.959966+00:00
-- url     : https://prove2.me/theorems/60490276-78b1-4db9-b548-b421c502e54d
-- title:
--   Claim 5.7 — a sink strong end of size at most $\sigma$ has volume at most $\sigma^2$
-- statement:
--   Let $G$ be a simple bipartite graph and $M$ any matching of $G$. For every sink strong end $U$ of $G$ with $|U|\le\sigma$,
--   $$\mathrm{vol}_{G_M}(U)\le\sigma^2,$$
--   where the volume is the sum over $v\in U$ of the out-degree of $v$ in the alternating digraph $G_M$.
--
--   The bound lets the local algorithm of §5 certify small strong ends with searches that stop after $\sigma^2$ arcs.
--
--   **Formalization Note** The sink strong end is defined through some matching (Definition 2.1), which may differ from $M$.
--
--   Differences from the source:
--   - reading: G, the graph of §5.2, in which parallel edges are suppressed → G is simple (a hypothesis); reason: §5.2 states "We suppress parallel edges" and the proof uses simplicity
--   - generalization: G the 2-edge-connected quotient on which §5 runs (the standing reduction of §2.1, p.3) → every well-formed simple bipartite graph; reason: the proof uses only simplicity and the sink condition N_G(U_L) = U_R; on 2-edge-connected graphs the Lean statement is the source's
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Claim 5.7, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd

set_option autoImplicit false

namespace BipDijoin

/-- **Claim 5.7** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.18 = PDF p.20). "Let M be any matching of the graph G and G_M be the directed graph constructed as
defined above. For any sink strong end U of size at most σ, we have vol_{G_M}(U) ≤ σ²."

For every well-formed simple bipartite graph `G`, every matching `M` of `G`, every sink strong end
`U` of `G` and every `σ ∈ ℕ` with `|U| ≤ σ`: the sum over `v ∈ U` of the out-degree of `v` in `G_M`
is at most `σ²`.

**Formalization Note.** §5.2 assumes simplicity ("We suppress parallel edges", p.18), so `G` is
simple. The out-degree counts every edge leaving a left vertex and the reverse arc of the matching
edge at a right vertex, in all of `G_M`. -/
theorem claim_5_7 (G : BipGraph) (hG : G.WF) (hs : G.Simple) (M : Finset ℕ) (hM : G.IsMatching M)
    (U : Finset ℕ) (hU : G.IsSinkEnd U) (σ : ℕ) (hσ : U.card ≤ σ) :
    G.vol M U ≤ σ ^ 2 := by sorry

end BipDijoin
