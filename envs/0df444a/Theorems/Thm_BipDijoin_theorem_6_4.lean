-- Prove2me | Theorems.Thm_BipDijoin_theorem_6_4
-- name    : BipDijoin.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:50:12.895969+00:00
-- url     : https://prove2.me/theorems/38443efb-9aac-4e67-ae11-3ad9d58226c2
-- title:
--   Theorem 6.4 — Algorithm 3 yields a partial relaxed end decomposition ending perfectly matchable (corrected: no isolated vertex)
-- statement:
--   Let $G$ be a $V_\infty$-irreducible bipartite multigraph, $d=|R|-|L|$, and run Algorithm 3 from a maximum matching $M_0$ with all vertices active, making any choice of source SCC and of shortest path at each iteration. Then:
--
--   1. every run has at most $|R|$ iterations;
--   2. if $G$ has no isolated vertex, the process never gets stuck: every state with a nonempty active set has a next iteration;
--   3. every complete run (active set empty) records a partial relaxed end decomposition of $G$ ending at its final graph $H$, its final matching is a perfect matching of $H$,
--   $$|V(H)|\le|V(G)|-d,$$
--   and exactly $d$ of its iterations augment.
--
--   The theorem is the correctness of the abstract many-terminal process; Lemmas 6.5 and 6.9 bound the total length of its augmenting paths.
--
--   **Formalization Note** The process keeps deactivated vertices in the graph, as Algorithm 3 does.
--
--   Differences from the source:
--   - correction: Algorithm 3 outputs a partial relaxed end decomposition ending with a perfectly matchable graph, for every V∞-irreducible G → the non-stuck clause assumes G has no isolated vertex; reason: counterexample: L = {ℓ}, R = {r₁, r₂, r₃}, edges ℓr₁ and ℓr₂, r₃ isolated; G is V∞-irreducible with d = 2, and after contracting {ℓ, r₁} with augmentation to r₂ and deactivating the reach of the new vertex, A = {r₃} has no nontrivial source SCC
--   - generalization: the run of Algorithm 3 with MaximumMatching and the subroutines of §6.4 → every run of the step relation: any initial maximum matching, any nontrivial source SCC of D_i[A_i], any shortest path; reason: each implementation makes one of these choices, so the Lean statement specializes to the source's
--   - encoding: terminates after at most |R| iterations; outputs Γ, H, M → every run has at most |R| steps, no state with A ≠ ∅ is stuck, and every run ending with A = ∅ satisfies the output clauses; reason: termination and output of a nondeterministic procedure as statements about its runs
--   - encoding: d = |R| − |L| and |V(G)| − d → integers (ℤ); reason: avoids truncated natural subtraction
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Theorem 6.4, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd
import Definitions.Def_BipDijoin_IsPartialDecomp
import Definitions.Def_BipDijoin_IsVinfIrreducible
import Definitions.Def_BipDijoin_CADStep

set_option autoImplicit false

namespace BipDijoin

/-- **Theorem 6.4** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.28 = PDF p.30). "Algorithm 3 outputs a partial relaxed end decomposition of G ending with a
perfectly matchable graph H with |V(H)| ≤ |V(G)|−d. It terminates after at most |R| iterations and
performs exactly d path augmentations."

Let `G` be a well-formed V∞-irreducible bipartite multigraph, `d = |R| − |L|` (an integer), `N₀` above
all vertex ids and `M₀` any maximum matching of `G`. For the runs of Algorithm 3 from
`(G, M₀, A = V(G))`, with every choice of source SCC and shortest path:
1. every run has at most `|R|` iterations;
2. if `G` has no isolated vertex, every state reached with `A ≠ ∅` has a next iteration (the
   process does not get stuck);
3. every complete run (one ending with `A = ∅`) records a partial relaxed end decomposition of `G`
   ending at its final graph `H`, its final matching is a perfect matching of `H`,
   `|V(H)| ≤ |V(G)| − d`, and exactly `d` of its iterations augment.

**Formalization Note.** Correction: clause 2 fails when `G` has an isolated vertex. Take
`L = {ℓ}`, `R = {r₁, r₂, r₃}`, edges `ℓr₁, ℓr₂`, `r₃` isolated: `G` is V∞-irreducible with `d = 2`;
after contracting `{ℓ, r₁}` and augmenting to `r₂`, and deactivating the reach of the new vertex,
`A = {r₃}` and no nontrivial source SCC exists, so the terminal graph never becomes perfectly
matchable. The hypothesis "no isolated vertex" is added to clause 2 only. The initial matching is
any maximum matching (Algorithm 3 computes one). -/
theorem theorem_6_4 (G : BipGraph) (hG : G.WF) (hirr : G.IsVinfIrreducible) (N₀ : ℕ)
    (hN₀ : ∀ v ∈ G.V, v < N₀) (M₀ : Finset ℕ) (hM₀ : G.IsMaxMatching M₀) :
    (∀ outs s, CADRun N₀ (cadStart G M₀) outs s → outs.length ≤ G.right.card) ∧
    (G.NoIsolated → ∀ outs s, CADRun N₀ (cadStart G M₀) outs s → s.A.Nonempty →
      ∃ o t, CADStep N₀ s o t) ∧
    (∀ outs s, CADRun N₀ (cadStart G M₀) outs s → s.A = ∅ →
      IsPartialDecomp false G N₀ (runRecs outs) s.H ∧ s.H.IsPerfectMatching s.M ∧
      (s.H.V.card : ℤ) ≤ (G.V.card : ℤ) - ((G.right.card : ℤ) - G.left.card) ∧
      ((runRecs outs).length : ℤ) = (G.right.card : ℤ) - G.left.card) := by sorry

end BipDijoin
