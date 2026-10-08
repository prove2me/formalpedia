-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_tableII_iff_fleetFeasible
-- name    : ClarkeWright64.Savings.tableII_iff_fleetFeasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:04:01.891364+00:00
-- url     : https://prove2.me/theorems/6321e837-be7f-405d-8a33-df156824f82c
-- title:
--   Computational procedure, condition (III), p. 573 — the Table II test holds exactly when the runs can be allocated to trucks
-- statement:
--   Suppose the capacities are ordered, $C_1<C_2<\dots<C_n$, and the smallest trucks are unlimited, $x_1=\infty$. Then for every finite multiset of run loads the following are equivalent:
--
--   1. the loads pass the Table II test: for each $i=1,\dots,n$,
--   $$
--   \#\{\text{runs with load} > C_i\}\le \sum_{k>i}x_k ;
--   $$
--   2. the runs can be allocated to the trucks: each run receives a truck of a class whose capacity is at least its load, and no class $i$ receives more than $x_i$ runs.
--
--   This is what justifies condition (III): checking the columns of Table II decides whether the amended routes are "consistent with truck availabilities and capacities".
--
--   **Formalization Note** Both standing assumptions of p. 569 are needed: without $x_1=\infty$ the untested column "Up to $C_1$" would bind, and without the order of the $C_i$ the columns are not nested.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), p. 573, Computational procedure, condition (III) and Table II; p. 569 (ordering of C_i, x_1 infinite)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Computational procedure, condition (III), p. 573: when
`C₁ < ⋯ < C_n` and `x₁ = ∞`, a multiset of run loads passes the Table II test exactly when the
runs can be allocated to the available trucks without exceeding any truck's capacity. -/
theorem tableII_iff_fleetFeasible {M n : ℕ} (I : Instance M n) (hC : StrictMono I.C)
    (hx : I.x 0 = ⊤) (loads : Multiset ℝ) :
    I.TableIIOK loads ↔ I.FleetFeasible loads := by sorry

end ClarkeWright64.Savings
