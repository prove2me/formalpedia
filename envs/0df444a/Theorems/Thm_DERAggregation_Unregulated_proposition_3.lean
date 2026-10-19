-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_proposition_3
-- name    : DERAggregation.Unregulated.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:00.421517+00:00
-- url     : https://prove2.me/theorems/a164470c-d4d1-4bd5-a853-050d55c17750
-- title:
--   Proposition 3, p. 14 — the aggregation dispatch (21) has an optimum consistent with Lemmas 3, 4 and (4) at its (5a)-multipliers
-- statement:
--   Consider the networked market under Assumptions 1 and 2, and assume the aggregation dispatch problem (21) is feasible (Assumption 4). Then (21) has an optimal solution $(h^*,x^*,d^*,y^*)$ with the following property. Let $\lambda$ be any vector of optimal Lagrange multipliers of (5a) at it.
--
--   1. For every prosumer $i$ whose node price $\lambda^{k(i)}$ is positive, with $z_i\in(0,Z)$ the root of $u_i'(z_i)=\lambda^{k(i)}$:
--      - $x_i^*=[C_i-z_i]^+$ and $d_i^*=[z_i-C_i]^+$;
--      - $(x^*_i,d^*_i)$ is an optimal response (Lemma 3) to the offer $P_i^*=[\lambda^{k(i)}(C_i-z_i)+u_i(z_i)-u_i(C_i)]^+$, $p_i^*=\lambda^{k(i)}$;
--      - this offer is optimal for the aggregator (Lemma 4): no offer $(P,p)\in\mathbb R^2_+$ yields a larger profit (13) against any optimal response of prosumer $i$.
--   2. For every generator $j$ whose node price is positive, $c_j'(y^*_j)=\lambda^{k(j)}$, i.e. (4) holds.
--
--   The ISO's dispatch of the aggregation model is therefore supported by the aggregator's equilibrium pricing and by price-taking generators: it is a competitive equilibrium of the aggregation market.
--
--   **Formalization Note** As in Proposition 1, the statements are made at nodes with a positive price, where the first-order conditions are solvable; the existence of multipliers is not claimed. "Consistent with Lemma 3 / Lemma 4" is stated as the explicit split of the dispatch, its optimality as a response to the offer (17a)–(17b), and the optimality of that offer for the aggregator.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 14, Proposition 3, Assumption 4 (p. 13); proof pp. 43–44

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

open Set

/-- Proposition 3 (p. 14). Under Assumptions 1, 2, 4 the aggregation dispatch (21) has an optimal
solution `(h*, x*, d*, y*)` such that, for every vector `λ` of optimal Lagrange multipliers of (5a)
at it: at every prosumer `i` with `λ^{loc i} > 0` and the root `z_i` of `u_i'(z_i) = λ^{loc i}`,
`(x*_i, d*_i) = ([C_i − z_i]⁺, [z_i − C_i]⁺)` is an optimal response (Lemma 3) to the offer
`(P*_i, p*_i) = ([λ(C_i − z_i) + u_i(z_i) − u_i(C_i)]⁺, λ^{loc i})`, and that offer is optimal for
the aggregator against every nonnegative offer and every optimal response (Lemma 4); at every
generator `j` with `λ^{gloc j} > 0`, `y*_j` satisfies (4). -/
theorem proposition_3 {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J]
    [Fintype L] (M : Market K I J L) (h1 : Assumption1 M) (h2 : Assumption2 M)
    (h4 : ∃ h x d y, FeasA M h x d y) :
    ∃ h x d y, IsOptA M h x d y ∧ ∀ lam : K → ℝ, IsMultA M lam h x d y →
      (∀ i, 0 < lam (M.loc i) → ∀ zz : ℝ, zz ∈ Ioo 0 M.Z → deriv (M.u i) zz = lam (M.loc i) →
        x i = max (M.C i - zz) 0 ∧ d i = max (zz - M.C i) 0 ∧
        IsResp (M.u i) (M.C i) M.Z (lam (M.loc i))
          (max (lam (M.loc i) * (M.C i - zz) + M.u i zz - M.u i (M.C i)) 0) (lam (M.loc i))
          (x i) (d i) ∧
        ∀ P' p' x' d' : ℝ, 0 ≤ P' → 0 ≤ p' →
          IsResp (M.u i) (M.C i) M.Z (lam (M.loc i)) P' p' x' d' →
          aggProfit (lam (M.loc i)) P' p' x' ≤
            aggProfit (lam (M.loc i))
              (max (lam (M.loc i) * (M.C i - zz) + M.u i zz - M.u i (M.C i)) 0)
              (lam (M.loc i)) (x i)) ∧
      (∀ j, 0 < lam (M.gloc j) → deriv (M.c j) (y j) = lam (M.gloc j)) := by sorry

end DERAggregation.Unregulated
