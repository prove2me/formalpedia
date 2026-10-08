-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_reachable_feasible
-- name    : ClarkeWright64.Savings.reachable_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:04:16.42278+00:00
-- url     : https://prove2.me/theorems/5b622eac-6720-4577-a9f7-828b41fe4d83
-- title:
--   Computational procedure, pp. 571 and 573 — every reachable state is a feasible allocation of the customers to trucks
-- statement:
--   Suppose $C_1<\dots<C_n$, $x_1=\infty$, and the initial allocation of one truck to each customer passes the Table II test (the paper's assumption that "an initial allocation of one vehicle to each customer is possible"). Then every state $S$ reached by the savings procedure
--
--   1. is an allocation: its runs are nonempty, avoid the depot, and cover every customer exactly once; and
--   2. is fleet feasible: its runs can be assigned to the available trucks without exceeding any capacity.
--
--   Thus every link the procedure makes produces "feasible routes consistent with truck availabilities and capacities".
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), p. 571, Theoretical aspects; pp. 572–573, Computational procedure

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Computational procedure, pp. 571 and 573: if `C₁ < ⋯ < C_n`,
`x₁ = ∞` and the initial allocation of one truck to each customer passes the Table II test,
then every state the procedure reaches is an allocation of the customers to runs that the
available trucks can carry. -/
theorem reachable_feasible {M n : ℕ} (I : Instance M n) (hC : StrictMono I.C)
    (hx : I.x 0 = ⊤) (hinit : I.TableIIOK ↑((init M).map I.runLoad))
    (s : State M) (hs : Reachable I s) :
    IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad) := by sorry

end ClarkeWright64.Savings
