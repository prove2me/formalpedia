-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_example_290
-- name    : ClarkeWright64.Savings.example_290
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:04:44.547425+00:00
-- url     : https://prove2.me/theorems/49deb4a0-b7b3-4dad-a5fc-ddc06ed44f76
-- title:
--   Computational procedure, the example, pp. 575–576 — every run on Table I ends with total distance 290
-- statement:
--   On the twelve-customer instance of Table I with the fleet of p. 573 (unlimited 4000-gallon trucks, three of 5000 gallons, four of 6000 gallons), every run of the savings procedure, whichever way the ties are broken, stops in a state whose runs serve the customer sets
--   $$
--   \{1,2,3,4\},\quad \{5\},\quad \{6,8,9\},\quad \{7,10,11,12\},
--   $$
--   with total distance $290$ units.
--
--   The paper reports the routes $P_0P_1P_2P_3P_4P_0$, $P_0P_5P_0$, $P_0P_6P_8P_9P_0$, $P_0P_{10}P_{12}P_{11}P_7P_0$. The order of customers within a run depends on the tie-breaks, so only the partition and the total are stated.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), pp. 575–576, Computational procedure (Tables V, VI and the routes)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure
import Definitions.Def_ClarkeWright64_Savings_TableI

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), the numerical example, pp. 575–576: on the data of Table I with
the fleet of p. 573, every run of the procedure (every tie-break) stops with the customers
partitioned into the runs `{1,2,3,4}`, `{5}`, `{6,8,9}`, `{7,10,11,12}` and a total
distance of 290 units. -/
theorem example_290 (s : State 12) (hs : Reachable tableI s) (hterm : Terminal tableI s) :
    tableI.mileage s = 290 ∧
    (↑(s.map List.toFinset) : Multiset (Finset (Fin 13))) =
      {{1, 2, 3, 4}, {5}, {6, 8, 9}, {7, 10, 11, 12}} := by sorry

end ClarkeWright64.Savings
