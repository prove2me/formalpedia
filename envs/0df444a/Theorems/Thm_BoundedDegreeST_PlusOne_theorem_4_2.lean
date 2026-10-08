-- Prove2me | Theorems.Thm_BoundedDegreeST_PlusOne_theorem_4_2
-- name    : BoundedDegreeST.PlusOne.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:02.925155+00:00
-- url     : https://prove2.me/theorems/b2452e42-f046-4c0c-87d1-5d271f3d5d22
-- title:
--   Theorem 4.2 — connecting tree of LP cost and degree B + 1
-- statement:
--   Let $(E,B,W,F)$ be a well-formed connecting-tree instance with a feasible LP-MBDCT solution and any real edge costs. The Figure 4 algorithm has a terminating run. Every run has at most $|V|-|F|-1+|W|$ iterations, and every returned set $H$ is an $F$-tree drawn from $E$ with
--
--   $$
--   \deg_H(v)\le B_v+1\quad(v\in W),\qquad
--   c(H)\le\sum_{e\in E}c_e x_e\quad\text{for every LP-feasible }x.
--   $$
--
--   The LP bound includes the optimum and supports the spanning-tree theorem at $F=\varnothing$, $W=V$.
--
--   **Formalization Note** LP feasibility makes the oracle step available. The theorem states run existence and a bound for every possible step chain so the return guarantee is not vacuous; it does not formalize the ellipsoid running time.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 666, Theorem 4.2

import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Theorem 4.2, p. 666, with the recursion and LP bound explicit. -/
theorem theorem_4_2 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I : Instance V)
    (hvalid : Valid I) (hfeasible : ∃ x, Feasible I.E I.B I.W I.F x) :
    (∃ H, Returns c I H) ∧
    (∀ k, Chain c I k →
      (k : ℤ) ≤ (Fintype.card V : ℤ) - (I.F.card : ℤ) - 1 + (I.W.card : ℤ)) ∧
    (∀ H, Returns c I H →
      H ⊆ I.E ∧ IsSpanningTree (H ∪ I.F) ∧
      (∀ v ∈ I.W, (degree H v : ℤ) ≤ I.B v + 1) ∧
      (∀ x, Feasible I.E I.B I.W I.F x →
        cost c H ≤ ∑ e ∈ I.E, c e * x e)) := by sorry
end BoundedDegreeST.PlusOne
