-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_eulerian_short_cycle
-- name    : BinaryThreeLCC.Main.eulerian_short_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:50.170386+00:00
-- url     : https://prove2.me/theorems/9dac2824-072e-4dc9-9d55-57c4b917b8a6
-- title:
--   Fact 3.4 — short directed cycle in an Eulerian graph
-- statement:
--   Let $D=(V,F)$ be a finite directed graph with no parallel directed edges and at least one edge. Suppose every vertex has equal incoming and outgoing degree. Then there is a directed cycle of length $\ell$ with
--
--   $$1\le\ell\le\frac{6|V|^2}{|F|}.$$
--
--   The vertices of the cycle are distinct, as are its edge identities; a directed self-loop is a cycle of length one. This retains the exact constant $6$ and the source's balance-only meaning of Eulerian.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - encoding: 6|V|²/|F| → the formula on |F| > 0; reason: the displayed denominator requires an edge; it is not assigned Lean division-by-zero semantics
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Fact 3.4, printed p. 9, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Graphs

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Fact 3.4, on the defined domain of its denominator. -/
theorem eulerian_short_cycle {V E : Type} [Fintype V] [Fintype E]
    (G : ContPatrol.Multigraph V E) (hEuler : Eulerian G) (hparallel : NoParallel G)
    (hedges : 0 < Fintype.card E) :
    ∃ (l : ℕ) (v : Fin l → V) (e : Fin l → E),
      DirectedCycle G l v e ∧
      (l : ℝ) ≤ 6 * (Fintype.card V : ℝ) ^ 2 / Fintype.card E := by sorry

end BinaryThreeLCC.Main
