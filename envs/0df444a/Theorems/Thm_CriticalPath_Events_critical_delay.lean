-- Prove2me | Theorems.Thm_CriticalPath_Events_critical_delay
-- name    : CriticalPath.Events.critical_delay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:27:49.876201+00:00
-- url     : https://prove2.me/theorems/e7c3c85c-c736-4561-a975-bd8f9ae68b47
-- title:
--   p. 163 — a delay in a critical job causes a comparable delay in the project completion time
-- statement:
--   Let $P$ be a project network with events $0,\dots,n$ and job durations $y_{ij}\in\mathbb R$, let $t^{(0)}$, $t^{(1)}$ be the earliest and latest event times of (1) and (2) for a completion time $\lambda \ge t_n^{(0)}$, and let $(i,j) \in P$ be a critical job. For $\delta \ge 0$ let $y'$ be the durations with $y'_{ij} = y_{ij} + \delta$ and $y'_{kl} = y_{kl}$ for every other pair, and let $t'^{(0)}$ be the earliest event times of (1) computed with $y'$. Then
--   $$
--   t'^{(0)}_n = t_n^{(0)} + \delta .
--   $$
--   That is, delaying a critical job by $\delta$ delays the earliest project completion time by exactly $\delta$.
--
--   **Formalization Note** The paper says a delay causes a "comparable" delay; this is read as the delay of the earliest completion time $t_n^{(0)}$ being exactly $\delta$. The delay $\delta$ is nonnegative, as a delay is.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, p. 163, §2 The Deterministic Case, sentence after the definition of a critical job

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

namespace CriticalPath.Events

/-- Kelley–Walker (1959), §2, p. 163: a delay in a critical job causes a comparable delay in
the project completion time. Read as: if `λ ≥ t_n^(0)`, the job `e ∈ P` is critical and
`δ ≥ 0`, then lengthening the duration of `e` by `δ` (all other durations unchanged) raises
the earliest terminus time by exactly `δ`. -/
theorem critical_delay {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam)
    (e : Fin (n + 1) × Fin (n + 1)) (he : e ∈ N.P) (hcrit : IsCritical N y lam e)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    earliest N (fun a b => if (a, b) = e then y a b + δ else y a b) (Fin.last n) =
      earliest N y (Fin.last n) + δ := by sorry

end CriticalPath.Events
