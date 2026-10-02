-- Prove2me | Theorems.Thm_CriticalPath_Events_critical_or_floater
-- name    : CriticalPath.Events.critical_or_floater
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:27:08.050523+00:00
-- url     : https://prove2.me/theorems/7df84836-0081-4880-b9d5-4b68643653d0
-- title:
--   p. 163 — every job is critical or a floater when λ ≥ t_n^(0)
-- statement:
--   Let $P$ be a project network with events $0,\dots,n$ and job durations $y_{ij}\in\mathbb R$, let $t^{(0)}$ and $t^{(1)}$ be the earliest and latest event times of (1) and (2), and suppose the project completion time satisfies $\lambda \ge t_n^{(0)}$. Then
--
--   1. every event occurs no later in the earliest schedule than in the latest one: $t_i^{(0)} \le t_i^{(1)}$ for every event $i$;
--   2. every job $(i,j) \in P$ is either critical or a floater, that is,
--   $$
--   t_j^{(1)} - t_i^{(0)} \ \ge\ y_{ij},
--   $$
--   with equality exactly for the critical jobs.
--
--   The paper's two definitions ("critical" when the maximum time available equals the duration, "floater" when it exceeds it) classify every job only because the maximum time available never falls short of the duration; this theorem states that fact.
--
--   **Formalization Note** This is the claim implicit in the paper's dichotomy of jobs into critical jobs and floaters; the paper does not state it as a separate sentence.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, p. 163, §2 The Deterministic Case, table of job quantities (Maximum time available) and the definitions of critical job and floater

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

namespace CriticalPath.Events

/-- Kelley–Walker (1959), §2, p. 163: for a project completion time `λ ≥ t_n^(0)`, every
event's earliest time is at most its latest time, and every job is either critical (maximum
time available equals its duration) or a floater (maximum time available exceeds its
duration). -/
theorem critical_or_floater {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    (∀ i, earliest N y i ≤ latest N y lam i) ∧
      ∀ e ∈ N.P, IsCritical N y lam e ∨ IsFloater N y lam e := by sorry

end CriticalPath.Events
