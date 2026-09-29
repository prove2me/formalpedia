-- Prove2me | Theorems.Thm_CriticalPath_CostCurve_feasibleDurations_eq_Ici
-- name    : CriticalPath.CostCurve.feasibleDurations_eq_Ici
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:31:53.317709+00:00
-- url     : https://prove2.me/theorems/5326e4c3-9005-4e60-a5d0-f6bbe0f1b5a9
-- title:
--   §3, p. 165 — the completion time can be reduced exactly down to the all-crash earliest completion time
-- statement:
--   Let a project network with events $0,\dots,n$ and jobs $P$, and job data $0 \le d_{ij} \le D_{ij}$, $a_{ij} \le 0$, $b_{ij} \ge 0$ be given. Let $t_n^{(0)}(d)$ be the earliest project completion time (recursion (1)) when every job has its crash duration. Then the linear program (5), (8), (9) has a schedule for $\lambda$ exactly when $\lambda$ is at least this all-crash completion time:
--
--   $$
--   \Lambda = \{\lambda \in \mathbb{R} : \text{some } (y,t) \text{ satisfies (5), (8), (9)}\} = [\,t_n^{(0)}(d),\ \infty).
--   $$
--
--   This makes precise the paper's statement that the parametric reduction of the project completion time "is repeated until no further reduction in project completion time is possible", and it identifies the domain of the project cost curve.
--
--   **Formalization Note** The paper states this only implicitly, in the sentence quoted above; the reading $\Lambda = [t_n^{(0)}(d), \infty)$ is the precise content of "no further reduction is possible" together with the fact that the program stays feasible for larger $\lambda$.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 165, Part I §3 Minimum Project Costs, left column, end of the parametric procedure paragraph ("until no further reduction in project completion time is possible"); recursion (1) p. 163

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: the reduction of the project completion time stops at the
all-crash earliest completion time. The linear program (5), (8), (9) has a schedule for `lam`
exactly when `lam ≥ tₙ⁽⁰⁾(d)`. -/
theorem feasibleDurations_eq_Ici {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    feasibleDurations J = Set.Ici (earliest N J.d (Fin.last n)) := by sorry

end CriticalPath.CostCurve
