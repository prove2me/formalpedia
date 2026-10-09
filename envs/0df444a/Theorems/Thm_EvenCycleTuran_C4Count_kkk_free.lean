-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_kkk_free
-- name    : EvenCycleTuran.C4Count.kkk_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:07.832999+00:00
-- url     : https://prove2.me/theorems/52dbb704-2f13-49ce-b663-d5e373c4cfbc
-- title:
--   Proof of Claim 2, p. 13 — a C₂ₖ-free graph is K_{k,k}-free: any k vertices have ≤ k−1 common neighbours
-- statement:
--   Let $k\ge 2$ and let $G$ be a graph containing no cycle of length $2k$. Since $C_{2k}$ is a subgraph of $K_{k,k}$, $G$ is $K_{k,k}$-free; equivalently, for every set $S$ of $k$ vertices of $G$,
--
--   $$\Bigl|\bigcap_{s\in S}N(s)\Bigr|\le k-1.$$
--
--   This is the only property of $C_{2k}$-freeness that the proof of Claim 2 uses.
--
--   **Formalization Note** The common neighbourhood is `commonNbrs G S`, the set of vertices adjacent to every vertex of $S$; for $k\ge 1$ it is automatically disjoint from $S$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 13, proof of Claim 2, paragraph "Observe that G is K_{k,k}-free"

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- §4.1, p. 13: a C₂ₖ-free graph is `K_{k,k}`-free, so any `k` vertices have at most `k − 1`
common neighbours. -/
theorem kkk_free {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 2 ≤ k) (hG : (cycleGraph (2 * k)).Free G)
    (S : Finset V) (hS : #S = k) :
    #(commonNbrs G S) ≤ k - 1 := by sorry

end EvenCycleTuran.C4Count
