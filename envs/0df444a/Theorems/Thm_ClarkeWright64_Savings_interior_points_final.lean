-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_interior_points_final
-- name    : ClarkeWright64.Savings.interior_points_final
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:03:47.636451+00:00
-- url     : https://prove2.me/theorems/6faa3593-c7f1-411d-927d-4427143651c8
-- title:
--   Theoretical aspects, pp. 571–572 — links between customers are never severed; interior points are never reconsidered
-- statement:
--   Let $S$ be a state reached by the savings procedure and let $S'$ follow $S$ by one step. Then:
--
--   1. every link between two customers survives: if $t_{y,z}=1$ in $S$ for customers $P_y,P_z$, then $t_{y,z}=1$ in $S'$;
--   2. no customer's link count to the depot increases: $t_{y,0}(S')\le t_{y,0}(S)$;
--   3. a customer with $t_{y,0}=0$ in $S$ (one linked to two other customers) lies in no admissible cell of $S$ or of any state reached from $S$, so it is never considered again for linking.
--
--   This is the procedure's form of the paper's remark that the only links ever severed are those to $P_0$.
--
--   **Formalization Note** The paper argues this for its general scheme through "shadow costs"; only the conclusion is formalized, for the procedure of pp. 573–575.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), pp. 571–572, Theoretical aspects

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Theoretical aspects, pp. 571–572: in a step of the procedure from a
reachable state, (a) every link between two customers survives, (b) no `t_{y,0}` increases, and
(c) a customer with `t_{y,0} = 0` (linked to two customers) lies in no admissible cell of any
later state, so it is never considered again for linking. -/
theorem interior_points_final {M n : ℕ} (I : Instance M n) (s s' : State M)
    (hs : Reachable I s) (hstep : Step I s s') :
    (∀ y z : Fin (M + 1), y ≠ 0 → z ≠ 0 → t s y z = 1 → t s' y z = 1) ∧
    (∀ y : Fin (M + 1), y ≠ 0 → t s' y 0 ≤ t s y 0) ∧
    (∀ y : Fin (M + 1), y ≠ 0 → t s y 0 = 0 →
      ∀ s'' : State M, Relation.ReflTransGen (Step I) s s'' →
        ∀ z : Fin (M + 1), ¬ Admissible I s'' y z ∧ ¬ Admissible I s'' z y) := by sorry

end ClarkeWright64.Savings
