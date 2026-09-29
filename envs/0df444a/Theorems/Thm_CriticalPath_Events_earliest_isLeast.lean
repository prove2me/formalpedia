-- Prove2me | Theorems.Thm_CriticalPath_Events_earliest_isLeast
-- name    : CriticalPath.Events.earliest_isLeast
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:26:09.398986+00:00
-- url     : https://prove2.me/theorems/bef0e6a8-feef-4e2c-bb89-b4d63a200643
-- title:
--   (1), pp. 162–163 — the recursion (1) computes the earliest event times
-- statement:
--   Let $P$ be a project network with events $0,\dots,n$ and job durations $y_{ij}\in\mathbb R$, and let $t^{(0)}$ be computed by the recursion (1), $t_0^{(0)} = 0$ and $t_j^{(0)} = \max[y_{ij} + t_i^{(0)} \mid (i,j)\in P]$ for $j \ge 1$.
--
--   Call a vector of event times $t = (t_0,\dots,t_n) \in \mathbb R^{n+1}$ *admissible* if the project starts at time $0$ and each job fits between its end events:
--   $$
--   t_0 = 0 \quad\text{and}\quad y_{ij} \le t_j - t_i \ \text{ for every job } (i,j) \in P .
--   $$
--   Then $t^{(0)}$ is admissible, and every admissible $t$ satisfies $t^{(0)}_i \le t_i$ for every event $i$. That is, $t^{(0)}$ is the least admissible vector, and $t_i^{(0)}$ is the earliest time at which event $i$ can occur.
--
--   This is the sense in which (1) computes "earliest time occurances"; together with the analogous statement for (2) it underlies every claim about critical jobs.
--
--   **Formalization Note** "Earliest time occurance" is read as: least admissible vector in the pointwise order (`IsLeast` in the order of functions `Fin (n+1) → ℝ`). The job constraint $y_{ij} \le t_j - t_i$ is the paper's "each job … is fully completed before any of its successors can begin" (p. 161) and its constraint (8) of p. 165. No sign condition on the durations is assumed, as on the page.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, p. 162 (right column, last paragraph) and p. 163 (display (1)), §2 The Deterministic Case

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

namespace CriticalPath.Events

/-- Kelley–Walker (1959), §2, display (1), p. 163: the times computed by (1) are the earliest
event times, i.e. the least vector `t` with `t 0 = 0` in which every job `(i, j) ∈ P` fits,
`y i j ≤ t j - t i`. -/
theorem earliest_isLeast {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    IsLeast {t : Fin (n + 1) → ℝ | t 0 = 0 ∧ ∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1}
      (earliest N y) := by sorry

end CriticalPath.Events
