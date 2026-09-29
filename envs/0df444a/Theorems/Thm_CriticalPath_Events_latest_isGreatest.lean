-- Prove2me | Theorems.Thm_CriticalPath_Events_latest_isGreatest
-- name    : CriticalPath.Events.latest_isGreatest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:26:37.438639+00:00
-- url     : https://prove2.me/theorems/d8b90cff-311b-4f41-b146-641fe69b05e1
-- title:
--   (2), p. 163 — the recursion (2) computes the latest event times relative to λ
-- statement:
--   Let $P$ be a project network with events $0,\dots,n$, job durations $y_{ij}\in\mathbb R$, earliest event times $t^{(0)}$ from (1), and a project completion time $\lambda$ with $\lambda \ge t_n^{(0)}$. Let $t^{(1)}$ be computed by the recursion (2), $t_n^{(1)} = \lambda$ and $t_i^{(1)} = \min[t_j^{(1)} - y_{ij} \mid (i,j)\in P]$ for $i \le n-1$.
--
--   Call $t \in \mathbb R^{n+1}$ *admissible for $\lambda$* if the project is complete by time $\lambda$ and each job fits between its end events:
--   $$
--   t_n \le \lambda \quad\text{and}\quad y_{ij} \le t_j - t_i \ \text{ for every job } (i,j) \in P .
--   $$
--   Then $t_n^{(1)} = \lambda$, $t^{(1)}$ is admissible for $\lambda$, and every $t$ admissible for $\lambda$ satisfies $t_i \le t_i^{(1)}$ for every event $i$. So $t^{(1)}$ is the greatest admissible vector, and $t_i^{(1)}$ is the latest time at which event $i$ may occur relative to the completion time $\lambda$.
--
--   **Formalization Note** "Latest time … relative to a fixed project completion time" is read as: greatest vector (pointwise order, `IsGreatest`) among those with $t_n \le \lambda$ satisfying every job constraint. The hypothesis $\lambda \ge t_n^{(0)}$ is the page's; this characterisation does not need it.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, p. 163, §2 The Deterministic Case, display (2)

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

namespace CriticalPath.Events

/-- Kelley–Walker (1959), §2, display (2), p. 163: for a project completion time
`λ ≥ t_n^(0)`, the times computed by (2) are the latest event times relative to `λ`:
`t_n^(1) = λ`, and `t^(1)` is the greatest vector `t` with `t n ≤ λ` in which every job
`(i, j) ∈ P` fits, `y i j ≤ t j - t i`. -/
theorem latest_isGreatest {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    latest N y lam (Fin.last n) = lam ∧
      IsGreatest {t : Fin (n + 1) → ℝ | t (Fin.last n) ≤ lam ∧
          ∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1}
        (latest N y lam) := by sorry

end CriticalPath.Events
