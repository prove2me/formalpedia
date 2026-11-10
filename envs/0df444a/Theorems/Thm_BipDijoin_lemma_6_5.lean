-- Prove2me | Theorems.Thm_BipDijoin_lemma_6_5
-- name    : BipDijoin.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:57.231247+00:00
-- url     : https://prove2.me/theorems/a8d26c53-afd7-42af-a463-f3784e6b52ae
-- title:
--   Lemma 6.5 — the augmenting paths of Algorithm 3 have total length $O(n\log^2 n)$
-- statement:
--   There is an absolute constant $C>0$ such that, for every $V_\infty$-irreducible bipartite multigraph $G$ with $n$ vertices and every complete run of Algorithm 3 from a maximum matching, the augmenting paths $P_i$ of Line 8 satisfy
--   $$\sum_i |P_i|\le C\,n\ln^2 n.$$
--
--   The bound is what makes the dynamic implementation of §6.4 run in $\tilde O(m\sqrt n)$ total time, even though contractions delete matched vertices.
--
--   Differences from the source:
--   - encoding: Σ_{i=1}^{β} |P_i| = O(n log² n) → the sum of the path lengths of the contract-augment iterations is at most C·n·(ln n)² with one constant C > 0 chosen before the graph; reason: the usual reading of O(·); a deactivation has no path; the base of the logarithm only changes C
--   - generalization: the run of Algorithm 3 with its subroutines → every complete run of the step relation: any initial maximum matching, any source SCC, any shortest path; reason: each implementation makes one of these choices, so the Lean statement specializes to the source's
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Lemma 6.5, p.29 (PDF p.31); proved pp.32–33 (PDF pp.34–35)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsVinfIrreducible
import Definitions.Def_BipDijoin_CADStep

set_option autoImplicit false

namespace BipDijoin

/-- **Lemma 6.5** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.29 = PDF p.31; proved on pp.32–33 = PDF pp.34–35). "Let P_i denote the path obtained in Line 8 of
Algorithm 3 in iteration i, β be the total number of iterations. Σ_{i=1}^{β} |P_i| = O(n log² n)"

There is a constant `C > 0` such that, for every well-formed V∞-irreducible bipartite multigraph
`G` with `n = |V(G)|`, every maximum matching `M₀` and every complete run of Algorithm 3 from
`(G, M₀, V(G))`, the total length of the augmenting paths of the run is at most `C · n · (ln n)²`.

**Formalization Note.** `C` is chosen before the graph. `|P_i|` is the number of arcs; the sum is
over the contract-augment iterations (a deactivation has no path). The base of the logarithm only
changes `C`. -/
theorem lemma_6_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : BipGraph), G.WF → G.IsVinfIrreducible → ∀ N₀ : ℕ,
      (∀ v ∈ G.V, v < N₀) → ∀ M₀ : Finset ℕ, G.IsMaxMatching M₀ →
      ∀ outs s, CADRun N₀ (cadStart G M₀) outs s → s.A = ∅ →
        ((runPathLengths outs).sum : ℝ) ≤ C * G.V.card * Real.log G.V.card ^ 2 := by sorry

end BipDijoin
