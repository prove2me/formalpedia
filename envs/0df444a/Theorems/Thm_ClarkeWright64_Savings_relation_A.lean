-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_relation_A
-- name    : ClarkeWright64.Savings.relation_A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:03:33.228004+00:00
-- url     : https://prove2.me/theorems/c03836a9-ec0e-4cd8-b074-3b46973d5023
-- title:
--   Computational procedure, relation (A), p. 573 — every customer has Σ_{z≠y} t_{y,z} = 2 at every stage
-- statement:
--   In the initial basic solution every customer has $t_{y,0}=2$ ($y=1,\dots,M$). Moreover, at every state reached by the savings procedure, every customer $P_y$ satisfies relation (A):
--   $$
--   \sum_{z=0}^{y-1} t_{y,z}+\sum_{z=y+1}^{M} t_{y,z}=2 .
--   $$
--
--   Relation (A) says that each customer is joined to exactly two neighbours on its truck's route, the depot counting once for each side of a run it closes; it is what makes the matrix $t$ a valid description of a set of routes throughout the procedure.
--
--   **Formalization Note** The two sums of the printed display lack a "+" between them; the statement uses the sum, written $\sum_{z\neq y}t_{y,z}$, over $z=0,\dots,M$. The relation is stated for every reachable state, not for arbitrary lists of runs, for which it is false.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), p. 573, Computational procedure, relation (A)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Computational procedure, relation (A), p. 573: the initial basic
solution has `t_{y,0} = 2` for every customer, and at every state the procedure reaches, every
customer `P_y` has `∑_{z ≠ y} t_{y,z} = 2` (the sum includes `z = 0`). -/
theorem relation_A {M n : ℕ} (I : Instance M n) :
    (∀ y : Fin (M + 1), y ≠ 0 → t (init M) y 0 = 2) ∧
    ∀ s : State M, Reachable I s →
      ∀ y : Fin (M + 1), y ≠ 0 → ∑ z ∈ Finset.univ.erase y, t s y z = 2 := by sorry

end ClarkeWright64.Savings
