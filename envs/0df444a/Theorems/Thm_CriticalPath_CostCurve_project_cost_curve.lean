-- Prove2me | Theorems.Thm_CriticalPath_CostCurve_project_cost_curve
-- name    : CriticalPath.CostCurve.project_cost_curve
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:34:28.276461+00:00
-- url     : https://prove2.me/theorems/8fc0a7f8-af13-407f-b135-284ec8e86f23
-- title:
--   §3, p. 165 — the project cost curve is non-increasing, piecewise linear and convex
-- statement:
--   Let a project network with events $0,\dots,n$ and jobs $P$ be given, with crash and normal durations $0 \le d_{ij} \le D_{ij}$ and linear job costs $a_{ij} y_{ij} + b_{ij}$, $a_{ij} \le 0$, $b_{ij} \ge 0$. For a completion time $\lambda$ consider the linear program
--
--   $$
--   C(\lambda) = \min \sum_{(i,j)\in P} (a_{ij} y_{ij} + b_{ij}) \quad \text{s.t.}\quad d_{ij} \le y_{ij} \le D_{ij},\ \ y_{ij} \le t_j - t_i\ \ ((i,j)\in P),\ \ t_0 = 0,\ \ t_n = \lambda,
--   $$
--
--   and let $\Lambda$ be the set of $\lambda$ for which it is feasible. Let $C : \mathbb{R} \to \mathbb{R}$ be any function whose value at every $\lambda \in \Lambda$ is this minimum. Then, on $\Lambda$, the **project cost curve** $C$ is
--
--   1. non-increasing,
--   2. piecewise linear, with finitely many affine pieces covering $\Lambda$, and
--   3. convex.
--
--   The project cost curve is the trade-off between project duration and direct cost that Kelley and Walker's parametric procedure traces and that management compares against indirect costs and market losses.
--
--   **Formalization Note** $C$ is taken as a function whose values on $\Lambda$ are the minima (`IsLeast`); its values off $\Lambda$ are irrelevant and every conclusion is stated on $\Lambda$ only. That the minimum exists for every $\lambda \in \Lambda$ is the milestone `exists_least_cost`, so the hypothesis on $C$ is satisfiable. Piecewise linearity is `IsPiecewiseLinearOn`: finitely many breakpoints, affine pieces between consecutive breakpoints and an unbounded last piece.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 165, Part I §3 Minimum Project Costs, right column, paragraph under Fig. 3 ("a non-increasing, piecewise linear, convex function ... called the project cost curve")

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule
import Definitions.Def_CriticalPath_CostCurve_IsPiecewiseLinearOn

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: the project cost curve `C(lam)`, the minimum of (7)
subject to (5), (8), (9), is on the set `Λ` of feasible completion times a non-increasing,
piecewise linear (finitely many affine pieces covering `Λ`), convex function. -/
theorem project_cost_curve {n : ℕ} (N : ProjectNetwork n) (J : JobData N) (C : ℝ → ℝ)
    (hC : ∀ lam ∈ feasibleDurations J, IsLeast (costSet J lam) (C lam)) :
    AntitoneOn C (feasibleDurations J) ∧
      IsPiecewiseLinearOn C (feasibleDurations J) ∧
      ConvexOn ℝ (feasibleDurations J) C := by sorry

end CriticalPath.CostCurve
