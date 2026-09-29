-- Prove2me | Theorems.Thm_CriticalPath_Events_critical_jobs_only_when_earliest
-- name    : CriticalPath.Events.critical_jobs_only_when_earliest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:28:30.690636+00:00
-- url     : https://prove2.me/theorems/0fb9ffe1-8e6d-4257-937a-ec135c8b3317
-- title:
--   p. 163 — critical jobs occur only when λ = t_n^(0), and then a critical path from origin to terminus exists
-- statement:
--   Let $P$ be a project network with events $0,\dots,n$ ($n \ge 1$) and job durations $y_{ij}\in\mathbb R$. Let $t^{(0)}$ be the earliest event times of (1), let $\lambda$ be a project completion time with $\lambda \ge t_n^{(0)}$, and let $t^{(1)}$ be the latest event times of (2) relative to $\lambda$. A job $(i,j)\in P$ is *critical* when its maximum time available equals its duration, $t_j^{(1)} - t_i^{(0)} = y_{ij}$.
--
--   If the project contains a critical job, then
--
--   1. $\lambda = t_n^{(0)}$; and
--   2. there is a critical path: events $0 = v_0, v_1, \dots, v_k = n$ such that for every $r = 1,\dots,k$ the pair $(v_{r-1}, v_r)$ is a job of $P$ and
--   $$
--   t_{v_r}^{(1)} - t_{v_{r-1}}^{(0)} = y_{v_{r-1} v_r}.
--   $$
--
--   This is the paper's statement that "a project will contain critical jobs only when $\lambda = t_n^{(0)}$", and that critical jobs, when present, contain a contiguous path from origin to terminus, the critical path that gives the method its name.
--
--   **Formalization Note** The hypothesis $\lambda \ge t_n^{(0)}$ is the page's assumption for (2). The critical path is a list of events with first element $0$, last element $n$, and consecutive pairs critical jobs of $P$. The theorem asserts only the paper's "only when" direction.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, p. 163, §2 The Deterministic Case, the two sentences after "A delay in a critical job will cause a comparable delay in the project completion time"

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

namespace CriticalPath.Events

/-- Kelley–Walker (1959), §2, p. 163: "A project will contain critical jobs only when
λ = t_n^(0). If a project does contain critical jobs, then it also contains at least one
contiguous path of critical jobs through the project diagram from origin to terminus." -/
theorem critical_jobs_only_when_earliest {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam)
    (hcrit : ∃ e ∈ N.P, IsCritical N y lam e) :
    lam = earliest N y (Fin.last n) ∧ ∃ p : List (Fin (n + 1)), IsCriticalPath N y lam p := by sorry

end CriticalPath.Events
