-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_theorem_1
-- name    : DERAggregation.Unregulated.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:09.716095+00:00
-- url     : https://prove2.me/theorems/b9af457c-1da5-4967-9c9d-9f13723b2d2f
-- title:
--   Theorem 1, p. 14 — the unregulated aggregation model attains the benchmark welfare, dispatch and wholesale prices
-- statement:
--   Consider the networked market under Assumptions 1 and 2, and assume the benchmark dispatch (9) is feasible (Assumption 3). Let $(h^*_B,z^*_B,y^*_B)$ be the optimal solution of (9) and $\mathcal W_B^*$ its welfare. Then:
--
--   1. the aggregation dispatch (21) has an optimal solution;
--   2. every optimal solution $(h_A,x_A,d_A,y_A)$ of (21) has welfare
--   $$\mathcal W_A^*=\mathcal W_B^*,\tag{22}$$
--   and the same dispatch as the benchmark: $x_A-d_A=z^*_B$, $y_A=y^*_B$, $h_A=h^*_B$;
--   3. the split $x^*=[z^*_B]^+$, $d^*=[-z^*_B]^+$ (with $h^*_B$, $y^*_B$) is an optimal solution of (21);
--   4. the wholesale prices coincide: a vector $\lambda$ is a vector of optimal Lagrange multipliers of (5a) at an optimal solution of (21) if and only if it is one at an optimal solution of (9).
--
--   Hence a monopolistic, profit-seeking aggregator using two-part pricing causes no loss of market efficiency: welfare, dispatch and locational prices are those of direct participation.
--
--   **Formalization Note** Theorem 1 names no assumptions; it is stated under Assumptions 1–3, which the paper's proof uses through Propositions 1 and 3 (Assumption 4 follows from Assumption 3 via the split). Problem (21) determines only the net sales $x-d$, not $x$ and $d$ separately; "the optimal $x^*,d^*,y^*$ … are the same as those solving (9)" is stated as items 2 and 3. Problem (21) is written in the separate variables $x$, $d$ with the constraints (18) as printed.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 14, Theorem 1, (22); proof pp. 43–44 (proof of Proposition 3)

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

/-- Theorem 1 (p. 14). Under Assumptions 1–3, with `(h*, z*, y*)` the optimal solution of the
benchmark dispatch (9): the aggregation dispatch (21) has an optimal solution; every optimal
solution of (21) has welfare `W*_A = W*_B` (22), `x − d = z*`, `y = y*`, `h = h*`; the split
`(h*, [z*]⁺, [−z*]⁺, y*)` is optimal for (21); and the wholesale prices (optimal Lagrange
multipliers of (5a)) of the two models coincide. -/
theorem theorem_1 {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J]
    [Fintype L] (M : Market K I J L) (h1 : Assumption1 M) (h2 : Assumption2 M)
    (h3 : ∃ h z y, FeasB M h z y) :
    ∃ hB zB yB, IsOptB M hB zB yB ∧
      (∃ hA xA dA yA, IsOptA M hA xA dA yA) ∧
      (∀ hA xA dA yA, IsOptA M hA xA dA yA →
        WA M xA dA yA = WB M zB yB ∧ (∀ i, xA i - dA i = zB i) ∧ yA = yB ∧ hA = hB) ∧
      IsOptA M hB (fun i => max (zB i) 0) (fun i => max (-zB i) 0) yB ∧
      (∀ lam : K → ℝ, IsPriceA M lam ↔ IsPriceB M lam) := by sorry

end DERAggregation.Unregulated
