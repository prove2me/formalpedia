-- Prove2me | Theorems.Thm_DRCVRP_FirstOrder_no_deterministic_reformulation
-- name    : DRCVRP.FirstOrder.no_deterministic_reformulation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T03:15:06.385868+00:00
-- url     : https://prove2.me/theorems/ebf40c4c-e21c-4489-b1c0-60a669a63391
-- title:
--   Theorem 4 — no deterministic CVRP reformulation over first-order generic ambiguity sets
-- statement:
--   There is an instance of the distributionally robust CVRP whose ambiguity set has the form of the first-order generic moment ambiguity set, that is, a number $n$ of customers, a number $m$ of vehicles of capacity $Q>0$, a risk level $\epsilon\in(0,1)$, a support box $[\underline{\boldsymbol q},\overline{\boldsymbol q}]$ with $\underline{\boldsymbol q}\ge\mathbf 0$, a mean $\boldsymbol\mu$ in the interior of the box, customer subsets $S_1,\dots,S_p$ and bounds $\boldsymbol\nu>\mathbf 0$, with the following property: for every deterministic CVRP instance with the same customers and vehicles, i.e. every capacity $Q'\ge0$ and every demand vector $\boldsymbol q'\in\mathbb R^n_+$,
--
--   $$
--   \bigl\{\mathbf R\in\mathfrak P(V_C,m):\mathbf R\text{ feasible in }\mathrm{RVRP}(\mathcal P)\bigr\}\ \ne\ \bigl\{\mathbf R\in\mathfrak P(V_C,m):\textstyle\sum_{i\in\mathbf R_k}q'_i\le Q'\ \forall k\bigr\}.
--   $$
--
--   This contrasts with marginalized moment ambiguity sets, over which the distributionally robust CVRP is equivalent to a deterministic CVRP with altered demands: once the ambiguity set couples the demands of different customers, the feasible route sets need not be those of any deterministic instance.
--
--   **Formalization Note** Route sets are `R : Fin m → List (Fin n)`; feasibility in $\mathrm{RVRP}(\mathcal P)$ requires $\mathbb P[\sum_{i\in\mathbf R_k}\tilde q_i\le Q]\ge1-\epsilon$ for every distribution in the ambiguity set and every vehicle. The paper takes $Q\in\mathbb R_+$; the statement asks for $Q>0$, which only restricts the witness.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, https://doi.org/10.1287/opre.2019.1924, §5.1, p. 726, Theorem 4; model of §2, pp. 718–719

import Mathlib
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_RouteSet

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Theorem 4 (§5.1, p. 726): there is an instance of the distributionally robust CVRP with an
ambiguity set of the form (12) (capacity `Q > 0`, risk level `ε ∈ (0,1)`, support `[qlo, qhi]`
with `qlo ≥ 0`, mean `μ` in the interior of the box, customer subsets `Sfam`, bounds `ν > 0`)
such that no deterministic CVRP instance with the same customers and vehicles (capacity
`Q' ≥ 0`, demands `q' ≥ 0`) has the same set of feasible route sets. -/
theorem no_deterministic_reformulation :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (p : ℕ) (Sfam : Fin p → Finset (Fin n))
      (ν : Fin p → ℝ),
      0 < Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      (∀ l, 0 < ν l) ∧
      ∀ (Q' : ℝ) (q' : Fin n → ℝ), 0 ≤ Q' → (∀ i, 0 ≤ q' i) →
        {R : Fin m → List (Fin n) |
            IsRVRPFeasible (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε Q R} ≠
          {R : Fin m → List (Fin n) | IsDeterministicFeasible Q' q' R} := by sorry

end DRCVRP.FirstOrder
