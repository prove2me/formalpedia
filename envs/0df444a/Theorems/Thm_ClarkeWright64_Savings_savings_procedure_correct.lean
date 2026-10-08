-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_savings_procedure_correct
-- name    : ClarkeWright64.Savings.savings_procedure_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:04:54.62864+00:00
-- url     : https://prove2.me/theorems/b170d26d-56f0-4d05-a22f-748e6d30e1c7
-- title:
--   Computational procedure, pp. 572–575 — every run of the savings procedure stops in a feasible truck allocation whose mileage is the initial mileage less the linked savings
-- statement:
--   Let the distances $d_{y,z}$ be symmetric, let the capacities satisfy $C_1<\dots<C_n$, let the trucks of the smallest capacity be unlimited ($x_1=\infty$), and suppose the initial allocation of one truck to each customer passes the Table II test. Then the savings procedure of Clarke and Wright has the following properties.
--
--   1. **Every run is finite**: whatever ties are broken, there is no infinite sequence of steps from the initial basic solution.
--   2. **No run stops early**: at every reachable state at which some cell is admissible, a cell of maximum saving among the admissible ones exists and can be linked.
--   3. **The output is feasible**: every final state (no more links possible) is an allocation of all customers to runs that the available trucks can carry.
--   4. **Relation (A)** holds at every final state: $\sum_{z\ne y}t_{y,z}=2$ for every customer $P_y$.
--   5. **Mileage**: every final state has total distance
--   $$
--   2\sum_{j=1}^{M} d_{0,j}\;-\sum_{\substack{1\le y<z\le M\\ t_{y,z}=1}}\bigl(d_{0,y}+d_{0,z}-d_{y,z}\bigr),
--   $$
--   the mileage of the initial basic solution less the savings of the linked cells of the half matrix.
--
--   **Formalization Note** The procedure is a relation (ties are free), so the theorem holds for every run. Clauses 1 and 2 rule out a procedure that does nothing. The distances need not be nonnegative or satisfy the triangle inequality, and savings may be negative; the procedure links the maximum admissible saving regardless of sign, as on p. 575.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), pp. 572–575, Computational procedure

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Computational procedure, pp. 572–575. For symmetric distances,
`C₁ < ⋯ < C_n`, `x₁ = ∞`, and an initial allocation of one truck per customer that passes the
Table II test:
1. every run of the procedure is finite (whatever the tie-breaks);
2. a reachable state from which some cell is admissible always has a successor;
3. every final state is an allocation of the customers that the available trucks can carry;
4. every final state satisfies relation (A);
5. the mileage of every final state is `2 ∑_j d_{0,j}` less the savings of the linked cells
   `(y:z)`, `y < z`. -/
theorem savings_procedure_correct {M n : ℕ} (I : Instance M n)
    (hsymm : ∀ i j, I.d i j = I.d j i) (hC : StrictMono I.C) (hx : I.x 0 = ⊤)
    (hinit : I.TableIIOK ↑((init M).map I.runLoad)) :
    Acc (fun s' s => Step I s s') (init M) ∧
    (∀ s : State M, Reachable I s → ¬ Terminal I s → ∃ s', Step I s s') ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad)) ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      ∀ y : Fin (M + 1), y ≠ 0 → ∑ z ∈ Finset.univ.erase y, t s y z = 2) ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      I.mileage s = ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), 2 * I.d 0 j -
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
            (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t s p.1 p.2 = 1),
          I.saving p.1 p.2) := by sorry

end ClarkeWright64.Savings
