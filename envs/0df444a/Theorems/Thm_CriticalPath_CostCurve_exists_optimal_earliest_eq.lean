-- Prove2me | Theorems.Thm_CriticalPath_CostCurve_exists_optimal_earliest_eq
-- name    : CriticalPath.CostCurve.exists_optimal_earliest_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:33:44.254275+00:00
-- url     : https://prove2.me/theorems/a6e13aea-aa88-4764-846d-897638dc1b4b
-- title:
--   §3, p. 165 — within the limits of most interest, λ is also the earliest project completion time
-- statement:
--   Let a project network with jobs $P$ and job data $0 \le d_{ij} \le D_{ij}$, $a_{ij} \le 0$, $b_{ij} \ge 0$ be given, and write $\lambda_c = t_n^{(0)}(d)$ and $\lambda_N = t_n^{(0)}(D)$ for the all-crash and all-normal earliest project completion times. For every $\lambda$ with
--
--   $$
--   \lambda_c \le \lambda \le \lambda_N
--   $$
--
--   there is a minimum cost schedule $(y,t)$ for $\lambda$ whose durations have earliest project completion time exactly $\lambda$: $t_n^{(0)}(y) = \lambda$.
--
--   Thus, in the range the parametric procedure traverses, the parameter $\lambda$ of the linear program is the completion time plotted on the project cost curve.
--
--   **Formalization Note** "Within the limits of most interest" is read as $\lambda_c \le \lambda \le \lambda_N$; for $\lambda > \lambda_N$ no admissible durations reach completion time $\lambda$. The claim is that *some* minimum cost schedule has this property, not every one: if all $a_{ij} = 0$, then $y = d$ is optimal for every $\lambda$ and has $t_n^{(0)}(d) = \lambda_c$.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 165, Part I §3 Minimum Project Costs, left column, paragraph after (9) ("within the limits of most interest, λ is also the earliest project completion time")

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: within the limits of most interest,
`tₙ⁽⁰⁾(d) ≤ lam ≤ tₙ⁽⁰⁾(D)`, some minimum cost schedule `(y, t)` for `lam` has earliest project
completion time `tₙ⁽⁰⁾(y) = lam`. -/
theorem exists_optimal_earliest_eq {n : ℕ} (N : ProjectNetwork n) (J : JobData N) (lam : ℝ)
    (hlo : earliest N J.d (Fin.last n) ≤ lam) (hhi : lam ≤ earliest N J.D (Fin.last n)) :
    ∃ (y : Fin (n + 1) → Fin (n + 1) → ℝ) (t : Fin (n + 1) → ℝ),
      IsOptimalSchedule J lam y t ∧ earliest N y (Fin.last n) = lam := by sorry

end CriticalPath.CostCurve
