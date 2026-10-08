-- Prove2me | Theorems.Thm_FlowJobShop_PairGroups_optimal_group_schedules_exist
-- name    : FlowJobShop.PairGroups.optimal_group_schedules_exist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:54:45.271136+00:00
-- url     : https://prove2.me/theorems/7d1ed988-c4b3-44cc-871d-c64b8436bee5
-- title:
--   §2, algorithm H — every flow shop on a group of at most two processors has an OFT schedule
-- statement:
--   Let $F$ be a flow shop with $m$ processors and $n$ jobs, and let $g\in\{1,\dots,\lceil m/2\rceil\}$. Then the flow shop $F_g$ on the processor group $\{P_{2g-1},P_{2g}\}$ (just $\{P_m\}$ for the last group when $m$ is odd) has an optimal finish time schedule: there is a feasible non-preemptive schedule $\rho$ of $F_g$ with
--   $$\mathrm{FT}(\rho)\le \mathrm{FT}(\rho')\quad\text{for every feasible schedule }\rho'\text{ of }F_g.$$
--
--   The paper obtains such a schedule with Johnson's $O(n\log n)$ algorithm. This statement guarantees that the optimal group schedules assumed in Lemma 11 exist, so that heuristic H is well defined on every instance.
--
--   **Formalization Note** Johnson's algorithm and its running time are not formalized; only the existence of an optimal schedule, which is what heuristic H uses, is stated.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 48, §2, description of algorithm H (Johnson's algorithm)

import Mathlib
import Definitions.Def_FlowJobShop_PairGroups_FlowShop
import Definitions.Def_FlowJobShop_PairGroups_AlgorithmH

namespace FlowJobShop.PairGroups

open FlowShop

/-- §2, description of algorithm H (p. 48): for every group `g` of at most two processors, the
flow shop on that group has an optimal finish time schedule (the paper obtains it with
Johnson's algorithm). -/
theorem optimal_group_schedules_exist {m n : ℕ} (F : FlowShop m n) (g : Fin ((m + 1) / 2)) :
    ∃ ρ : Fin (groupSize m g) → Fin n → ℝ, (F.group g).IsOptimal ρ := by sorry

end FlowJobShop.PairGroups
