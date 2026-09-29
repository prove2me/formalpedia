-- Prove2me | Theorems.Thm_CriticalPath_CostCurve_all_normal_optimal
-- name    : CriticalPath.CostCurve.all_normal_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:33:13.350784+00:00
-- url     : https://prove2.me/theorems/6be358d0-9946-4b19-befa-24ee1eb6e126
-- title:
--   §3, p. 165 — the all-normal solution is a minimum cost schedule for $\lambda = t_n^{(0)}$
-- statement:
--   Let a project network with jobs $P$ and job data $0 \le d_{ij} \le D_{ij}$, $a_{ij} \le 0$, $b_{ij} \ge 0$ be given. In the **all-normal solution** every job has its normal duration, $y_{ij} = D_{ij}$, and every job starts as early as possible, so the event times are the earliest event times $t^{(0)}(D)$ of recursion (1). Let
--
--   $$
--   \lambda_N = t_n^{(0)}(D).
--   $$
--
--   Then $(D, t^{(0)}(D))$ is a schedule for $\lambda_N$ (it satisfies (5), (8), (9)), and its cost (7) is at most the cost of every schedule for $\lambda_N$: it is a minimum cost schedule for $\lambda = t_n^{(0)}$.
--
--   This is the starting point of the parametric procedure that traces the project cost curve.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 165, Part I §3 Minimum Project Costs, left column ("By the nature of the job cost functions this schedule is also a minimum cost schedule for λ = t_n^(0)")

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: the all-normal solution `y = D`, with every job started as
early as possible (`t = t⁽⁰⁾(D)`), is a minimum cost schedule for `λ = tₙ⁽⁰⁾(D)`. -/
theorem all_normal_optimal {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    IsOptimalSchedule J (earliest N J.D (Fin.last n)) J.D (earliest N J.D) := by sorry

end CriticalPath.CostCurve
