-- Prove2me | Theorems.Thm_AllocationIndices_weighted_flow_time_equal_ratios
-- name    : AllocationIndices.weighted_flow_time_equal_ratios
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:39:21.750002+00:00
-- url     : https://prove2.me/theorems/6cd13dc0-d874-4166-b276-f63284280fab
-- title:
--   Theorem 3.3: with c_i/s_i constant on m machines, the weighted flow time is κ/2 (∑ s_i² + S²/m + ∑_j δ_j²), so minimizing it is minimizing ∑_j δ_j²
-- statement:
--   **Theorem 3.3.** For $m$ machines and $n$ deterministic jobs with $c_i/s_i$ the same for all jobs, minimization of weighted flow time is equivalent to minimization of $\sum_j \delta_j^2$, where $S/m + \delta_j$ is the total process time for machine $j$, and $S = \sum_i s_i$.
--
--   Formally, as the identity behind it: for every schedule $\sigma$ of $n$ jobs on $m \ge 1$ machines, service times $s_i$ and weights $c_i = \kappa s_i$ for a common $\kappa$,
--   $$\sum_i c_i C_i = \frac{\kappa}{2}\Big(\sum_i s_i^2 + \frac{S^2}{m} + \sum_{j=1}^m \delta_j^2\Big),$$
--   where $C_i$ is the completion time of job $i$ under $\sigma$ and $\delta_j$ the excess of machine $j$'s load over $S/m$. The first two terms do not depend on the schedule, so minimizing the weighted flow time over schedules is minimizing $\sum_j \delta_j^2$, which is the theorem; the identity also shows that the order of the jobs on a machine is irrelevant when all ratios agree.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §3.4.3 p. 64, Theorem 3.3 (proof left as Exercise 3.5)

import Definitions.Def_AllocationIndices_Jobs

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem weighted_flow_time_equal_ratios {n m : ℕ} (σ : Schedule n m) (s c : Fin n → ℝ)
    (hm : 0 < m) {κ : ℝ} (hc : ∀ i, c i = κ * s i) :
    weightedFlowTime σ s c =
      κ / 2 * (∑ i, s i ^ 2 + (∑ i, s i) ^ 2 / m + ∑ j, loadDeviation σ s j ^ 2) := by sorry

end AllocationIndices
