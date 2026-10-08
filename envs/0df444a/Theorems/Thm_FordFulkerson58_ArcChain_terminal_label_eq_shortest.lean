-- Prove2me | Theorems.Thm_FordFulkerson58_ArcChain_terminal_label_eq_shortest
-- name    : FordFulkerson58.ArcChain.terminal_label_eq_shortest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:27:51.872001+00:00
-- url     : https://prove2.me/theorems/352baac1-0f48-4caa-9ca1-2da1417e219e
-- title:
--   §3, p. 1780 — when the labeling process stops, π_i is the length of a shortest chain from S to P_i; the smallest π_i on T is the S-to-T distance
-- statement:
--   Let $N$ be a network with non-negative arc lengths $l_e$, let $S$ and $T$ be sets of nodes, and let $\pi$ be a labeling obtained from the initial labels ($0$ on $S$, $\infty$ elsewhere) by finitely many steps of the labeling process, such that no further step is possible. Then
--
--   1. for every node $v$, $\pi_v$ is the length of a shortest chain from $S$ to $v$ ($\infty$ if there is none);
--   2. the smallest label on $T$ is the length of a shortest chain from $S$ to $T$:
--   $$\min_{v \in T} \pi_v = \min\{\, \text{length}(C) : C \text{ a chain from } S \text{ to a node of } T \,\}.$$
--
--   This is the correctness of the shortest chain algorithm: the final labels are the shortest-chain distances from the source set.
--
--   **Formalization Note** The labeling must be both reachable from the initial labels and terminal; a terminal labeling alone (for instance all labels $0$) need not consist of distances. Both minima are $\infty$ (`⊤`) on empty sets.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), p. 1780, §3, the labeling process ("then the number π_i represents the length of a shortest chain from S to P_i … In particular")

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1780: when the labeling process (with non-negative lengths) stops, every label is the length
of a shortest chain from `S` to its node, and the smallest label on `T` is the length of a shortest
chain from `S` to `T`. -/
theorem terminal_label_eq_shortest {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S T : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (lab : V → WithTop ℝ)
    (hrun : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) (hterm : IsTerminal N l lab) :
    (∀ v, lab v = shortestChainLength N l S v) ∧ T.inf lab = shortestChainLengthTo N l S T := by sorry

end FordFulkerson58.ArcChain
