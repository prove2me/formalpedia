-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_minimal_cuts_union_inter
-- name    : FlowsNetworks.MaxFlow.minimal_cuts_union_inter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:14.301904+00:00
-- url     : https://prove2.me/theorems/2b1e4580-19e6-4000-8979-bd6cc2e992fc
-- title:
--   Chapter I, Corollary 5.4 — unions and intersections of minimal cuts are minimal cuts
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative capacities $c$ and let $s \neq t$. If $(X, \bar X)$ and $(Y, \bar Y)$ are minimal cuts separating $s$ and $t$, then
--   $$(X \cup Y, \overline{X \cup Y}) \quad\text{and}\quad (X \cap Y, \overline{X \cap Y})$$
--   are also minimal cuts.
--
--   So the source sides of minimal cuts form a lattice under union and intersection; in particular there is a smallest and a largest one, which Theorem 5.5 identifies.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$). Cuts are given by their node sets.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 23, Corollary 5.4

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Corollary 5.4 (p. 23): if `(X, X̄)` and
`(Y, Ȳ)` are minimal cuts, then `(X ∪ Y, (X ∪ Y)‾)` and `(X ∩ Y, (X ∩ Y)‾)` are also minimal
cuts. -/
theorem minimal_cuts_union_inter {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (X Y : Finset N)
    (hX : IsMinCut G s t X) (hY : IsMinCut G s t Y) :
    IsMinCut G s t (X ∪ Y) ∧ IsMinCut G s t (X ∩ Y) := by sorry

end FlowsNetworks.MaxFlow
