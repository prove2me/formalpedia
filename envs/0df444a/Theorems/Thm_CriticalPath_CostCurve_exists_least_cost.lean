-- Prove2me | Theorems.Thm_CriticalPath_CostCurve_exists_least_cost
-- name    : CriticalPath.CostCurve.exists_least_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:32:43.158447+00:00
-- url     : https://prove2.me/theorems/a04cf9b3-374f-4f2e-b1b0-0f8c078ebcdc
-- title:
--   §3, p. 165 — a least costly schedule exists for every feasible completion time
-- statement:
--   Let a project network with jobs $P$ and job data $0 \le d_{ij} \le D_{ij}$, $a_{ij} \le 0$, $b_{ij} \ge 0$ be given. For every feasible completion time $\lambda \in \Lambda$ the linear program
--
--   $$
--   \text{minimize } \sum_{(i,j)\in P} (a_{ij} y_{ij} + b_{ij}) \quad \text{subject to (5)},\ \ y_{ij} \le t_j - t_i\ \ ((i,j) \in P),\ \ t_0 = 0,\ t_n = \lambda
--   $$
--
--   attains its minimum: the set of costs of schedules for $\lambda$ has a least element.
--
--   This is what makes the project cost curve $C(\lambda)$, "the least costly schedule for any given feasible earliest project completion time", well defined on $\Lambda$.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 165, Part I §3 Minimum Project Costs, left column, top: the linear program with (8), (9)

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: for every feasible completion time `lam` the linear program
"minimize (7) subject to (5), (8), (9)" has a least costly schedule. -/
theorem exists_least_cost {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    ∀ lam ∈ feasibleDurations J, ∃ c : ℝ, IsLeast (costSet J lam) c := by sorry

end CriticalPath.CostCurve
