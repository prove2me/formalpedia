-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_tsp_case
-- name    : ClarkeWright64.Savings.tsp_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:04:27.095987+00:00
-- url     : https://prove2.me/theorems/30d5a8ac-74e1-464d-a3ca-25a171c0b6ec
-- title:
--   Formulation, p. 569 — if C_n ≥ Σ_j q_j the problem becomes the traveling salesman problem
-- statement:
--   Suppose the distances are shortest-route distances: $d$ is symmetric, nonnegative, zero on the diagonal and satisfies the triangle inequality. Suppose the largest capacity covers all the loads,
--   $$
--   C_n\ \ge\ \sum_{j=1}^{M} q_j ,
--   $$
--   and at least one truck of capacity $C_n$ is available. Then the least total mileage of a feasible allocation of the loads to trucks equals the length of a shortest traveling salesman tour through the depot and all the customers.
--
--   **Formalization Note** The printed sum has upper limit $j=n$, which is a misprint: $n$ counts truck classes, and the sum is over the $M$ customers. The availability of a truck of capacity $C_n$ is implied by the paper's "trucks ... are available" and is stated explicitly. The metric hypotheses come from p. 568, "the shortest route between every two points in the system is given".
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), p. 569, Formulation; p. 568 (shortest routes)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Formulation, p. 569: if the distances are shortest-route distances
(a metric) and the largest capacity `C_n` is at least the total load of all customers, with at
least one such truck available, the optimum of the problem equals the length of an optimal
traveling salesman tour through the depot and all customers. -/
theorem tsp_case {M n : ℕ} (I : Instance M n) (hd : SupplyChainTheory.VRPMetric I.d)
    (hcap : ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), I.q j ≤ I.C (Fin.last n))
    (htruck : 1 ≤ I.x (Fin.last n)) :
    optMileage I = SupplyChainTheory.tspOpt I.d := by sorry

end ClarkeWright64.Savings
