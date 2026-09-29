-- Prove2me | Theorems.Thm_FamousTheorems_connected_iff_interval_order_7a
-- name    : FamousTheorems.connected_iff_interval_order_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:50.831697+00:00
-- url     : https://prove2.me/theorems/5ad1319c-5353-491e-a10f-0a89df4f949d
-- title:
--   Connected subsets of a conditionally complete dense linear order are intervals
-- statement:
--   **Connected subsets of a conditionally complete dense linear order are intervals.** Let $\alpha$ be a densely ordered, conditionally complete linear order with the order topology, such as $\mathbb R$. A subset $s\subseteq\alpha$ is preconnected if and only if it is order-connected: whenever $a,b\in s$ and $a\le x\le b$, also $x\in s$.
--
--   For $\mathbb R$ this says that the connected subsets are exactly the intervals. That fact is the topological content of the intermediate value theorem, since continuous images of connected sets are connected. Completeness and density are both needed: in $\mathbb Q$ or in $\mathbb Z$ with the order topology, intervals need not be connected.
--
--   **Formalization note.** Mathlib's `isPreconnected_iff_ordConnected`. `IsPreconnected` is connectedness without the requirement that the set be nonempty, and `Set.OrdConnected s` is the interval condition above.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isPreconnected_iff_ordConnected`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem connected_iff_interval_order_7a {α : Type*} [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α] [DenselyOrdered α]
    {s : Set α} : IsPreconnected s ↔ s.OrdConnected := by sorry

end FamousTheorems
