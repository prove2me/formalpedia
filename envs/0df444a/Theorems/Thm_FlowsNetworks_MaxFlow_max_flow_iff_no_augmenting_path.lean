-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_max_flow_iff_no_augmenting_path
-- name    : FlowsNetworks.MaxFlow.max_flow_iff_no_augmenting_path
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:50.824995+00:00
-- url     : https://prove2.me/theorems/9f6e96c8-eacf-4aea-b7a9-efe4bd9cd0ee
-- title:
--   Chapter I, Corollary 5.2 — a flow is maximal iff there is no flow augmenting path
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative capacities $c$, let $s \neq t$ be two distinguished nodes, and let $f$ be a flow from $s$ to $t$ (of some value $v$). Then
--   $$f \text{ is maximal} \iff \text{there is no flow augmenting path from } s \text{ to } t \text{ with respect to } f,$$
--   where a flow augmenting path is a path $s = x_0, x_1, \dots, x_n = t$ of distinct nodes such that $f < c$ on its forward arcs and $f > 0$ on its reverse arcs.
--
--   The corollary says that to increase the value of a flow it suffices to look for improvements of a very restricted kind; it is the stopping rule of the labeling method.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$).
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 22, Corollary 5.2

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network
import Definitions.Def_FlowsNetworks_MaxFlow_AugmentingPath

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Corollary 5.2 (p. 22): a flow `f` is maximal
if and only if there is no flow augmenting path from `s` to `t` with respect to `f`. -/
theorem max_flow_iff_no_augmenting_path {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v) :
    IsMaxFlow G s t f ↔ ¬ HasFlowAugmentingPath G f s t := by sorry

end FlowsNetworks.MaxFlow
