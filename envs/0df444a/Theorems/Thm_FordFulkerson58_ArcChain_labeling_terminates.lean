-- Prove2me | Theorems.Thm_FordFulkerson58_ArcChain_labeling_terminates
-- name    : FordFulkerson58.ArcChain.labeling_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:27:52.966982+00:00
-- url     : https://prove2.me/theorems/a6e0a75c-3fc3-4b48-8ab0-07a276cc2c41
-- title:
--   §3, p. 1780, the labeling process — with lengths ≥ 0, every run of improving-arc replacements from the initial labels is finite
-- statement:
--   Let $N$ be a network whose arc lengths $l_e$ are all non-negative, and let $S$ be a set of nodes. Start the labeling process with $\pi_i = 0$ on $S$ and $\pi_i = \infty$ elsewhere, and repeatedly replace $\pi_j$ by $\pi_i + l_e$ whenever an arc $e$ traversable from $P_i$ to $P_j$ satisfies $\pi_i + l_e < \pi_j$. Then the process cannot go on forever: there is no infinite sequence of labelings
--   $$\pi^{(0)} = \text{initial labels},\quad \pi^{(0)} \to \pi^{(1)} \to \pi^{(2)} \to \cdots$$
--   in which each $\pi^{(t+1)}$ arises from $\pi^{(t)}$ by one such replacement.
--
--   This is the page's "Eventually no such arcs can be found": whatever order the arcs are scanned in, the process stops with a terminal labeling.
--
--   **Formalization Note** Lengths may be $0$; no strict positivity is assumed. The statement covers every run, not one chosen run.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), p. 1780, §3, the labeling process ("Eventually no such arcs can be found")

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1780, the labeling process: with non-negative arc lengths, every run of the labeling
process from the initial labels is finite — there is no infinite sequence of improving replacements. -/
theorem labeling_terminates {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) :
    ¬ ∃ f : ℕ → V → WithTop ℝ, f 0 = initLabel S ∧ ∀ i, RelaxStep N l (f i) (f (i + 1)) := by sorry

end FordFulkerson58.ArcChain
