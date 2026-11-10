-- Prove2me | Theorems.Thm_BipDijoin_lemma_6_9
-- name    : BipDijoin.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:50:03.109413+00:00
-- url     : https://prove2.me/theorems/a3d96989-a975-46d1-b0c4-58a4d626ea58
-- title:
--   Lemma 6.9 — at most $O(n\log n/h)$ augmenting paths longer than $h$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a $V_\infty$-irreducible bipartite multigraph with $n$ vertices and consider any complete run of Algorithm 3 from a maximum matching, with augmenting paths $P_1,P_2,\dots$. For every integer $h>4\ln n+1$,
--   $$N_h=\big|\{i:\ |P_i|>h\}\big|\le C\,\frac{n\ln n}{h}.$$
--
--   Together with a dyadic grouping of path lengths this gives Lemma 6.5, the $O(n\log^2 n)$ bound on the total augmentation length.
--
--   **Formalization Note** $n=|V(G)|$ ("Recall $n=|V(G_0)|$", p.33); the threshold uses the natural logarithm; $|P_i|$ counts arcs.
--
--   Differences from the source:
--   - encoding: N_h = O(n log n / h) → N_h ≤ C·n·ln n / h with one constant C > 0 chosen before the graph; reason: the usual reading of O(·), uniform over instances
--   - generalization: the run of Algorithm 3 with its subroutines → every complete run of the step relation: any initial maximum matching, any source SCC, any shortest path; reason: each implementation makes one of these choices, so the Lean statement specializes to the source's
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Lemma 6.9, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsVinfIrreducible
import Definitions.Def_BipDijoin_CADStep

set_option autoImplicit false

namespace BipDijoin

/-- **Lemma 6.9** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.32 = PDF p.34). "Let N_h := |{i : |P_i| > h}|. For every h > 4 ln n + 1, N_h = O(n log n / h)."

There is a constant `C > 0` such that, for every well-formed V∞-irreducible bipartite multigraph
`G` with `n = |V(G)|`, every maximum matching `M₀`, every complete run of Algorithm 3 from
`(G, M₀, V(G))` and every integer `h > 4 ln n + 1`, the number of augmenting paths `P_i` of the run
with `|P_i| > h` is at most `C · n · ln n / h`.

**Formalization Note.** `C` is chosen before the graph (one constant for all instances). The
threshold uses the natural logarithm, as printed; `h` is an integer ("Fix an integer h", p.31).
`|P_i|` is the number of arcs. Runs are those of the step relation `CADStep`, which keeps the
deactivated vertices in the graph as Algorithm 3 does. -/
theorem lemma_6_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : BipGraph), G.WF → G.IsVinfIrreducible → ∀ N₀ : ℕ,
      (∀ v ∈ G.V, v < N₀) → ∀ M₀ : Finset ℕ, G.IsMaxMatching M₀ →
      ∀ outs s, CADRun N₀ (cadStart G M₀) outs s → s.A = ∅ →
      ∀ h : ℕ, (h : ℝ) > 4 * Real.log G.V.card + 1 →
        (((runPathLengths outs).filter (fun l => h < l)).length : ℝ) ≤
          C * G.V.card * Real.log G.V.card / h := by sorry

end BipDijoin
