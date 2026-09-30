-- Prove2me | Theorems.Thm_Birge1985_Degeneracy_optimality_cuts_force_degeneracy
-- name    : Birge1985.Degeneracy.optimality_cuts_force_degeneracy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:32:29.643508+00:00
-- url     : https://prove2.me/theorems/3ccc7b77-4e2a-4538-8991-3b5e1541bb4e
-- title:
--   Proposition 4 — two binding optimality cuts force a degenerate optimal descendant solution
-- statement:
--   This is Proposition 4 of Birge (1985), the paper's degeneracy result for the optimality cuts of nested decomposition.
--
--   Let $P$ be the scenario problem (7) of scenario $j$ at period $t$, with decision $x \in \mathbb{R}^n$ and future-cost variable $\theta$, and let $J'$ be the finite set of its descendant scenarios at period $t+1$. Descendant $j'$ has the problem (7) $Q_{j'}$ whose (7.2) right-hand side is $\xi_{j'} + B_{j'} x$, and carries a weight $p_{j'} > 0$. Assume:
--
--   1. two optimality cuts $l_1, l_2$ of type (7.4) of $P$, $E_{l}^\top x + \theta \ge e_{l}$, are **distinct**: $(E_{l_1}, e_{l_1}) \ne (E_{l_2}, e_{l_2})$;
--   2. both are **valid**: $e_l - E_l^\top x \le \sum_{j'} p_{j'} (c_{j'}^\top y_{j'} + \theta_{j'})$ for every $x$ and every choice of feasible points $(y_{j'}, \theta_{j'})$ of the problems $Q_{j'}$ at $x$;
--   3. both are **binding** at a point $(\bar x, \bar\theta)$: $E_l^\top \bar x + \bar\theta = e_l$ for $l = l_1, l_2$;
--   4. for each $j' \in J'$, $z_{j'}$ is an optimal basic feasible solution of $Q_{j'}$ with $\bar x$ input in (7.2), and $\lambda_{j'}$ is an optimal dual vector of that problem;
--   5. the new optimality cut $E^\top x + \theta \ge e$ of NDSPA Step 3a built from these duals,
--   $$
--   E = -\sum_{j' \in J'} p_{j'}\, \pi_{j'}^\top B_{j'}, \qquad e = \sum_{j' \in J'} p_{j'} \bigl(\pi_{j'}^\top \xi_{j'} + \rho_{j'}^\top d_{j'} + \sigma_{j'}^\top e_{j'}\bigr),
--   $$
--   where $\pi_{j'}, \rho_{j'}, \sigma_{j'}$ are the parts of $\lambda_{j'}$ on the rows (7.2), (7.3), (7.4) of $Q_{j'}$, does **not** satisfy the test (9), i.e. $\bar\theta \ge e - E^\top \bar x$.
--
--   Then
--
--   $$
--   z_{j'} \text{ is a degenerate basic solution of } Q_{j'} \text{ for some } j' \in J'.
--   $$
--
--   Degeneracy is the general-form notion over the whole constraint family of (7), the free $\theta$ included. The result says that when the backward pass of NDSPA stalls (no new cut is added because (9) fails) at a point where two cuts bind, the descendants' simplex answers cannot all be nondegenerate; this is the mechanism behind the repeated solutions of Remark 4. The paper states it and refers its proof to Birge (1980).
--
--   **Formalization Note.** Readings of the paper's words: "two constraints of type (7.4)" are two distinct cuts, and both are valid lower bounds, the invariants NDSPA maintains (a cut is added only when (9) holds, and the descendants' feasible sets only shrink once the $\theta = 0$ restrictions are removed); without these two hypotheses the statement is false. "Some solution $(\bar x, \bar\theta)$ of (7)" is read as any point at which both rows hold with equality (feasibility or optimality for $P$ is not required, which strengthens the statement). "Every set of optimal solutions … that produces $E$ and $e$" is read as one optimal basic feasible solution and one optimal dual vector per descendant, the cut being computed from those duals. The Step 3a formula is completed: the paper prints $E = -\sum \pi B_t$ and $e = \sum \pi\,\xi$, omitting the weights and the terms $\rho^\top d + \sigma^\top e$; the weights $p_{j'} > 0$ are arbitrary positive numbers (conditional probabilities are a special case, and $p \equiv 1$ is the printed sum).
-- source:
--   Birge, Decomposition and Partitioning Methods for Multistage Stochastic Linear Programs, Operations Research 33(5), 1985, p. 997, Proposition 4 (with NDSPA Step 3a and test (9), p. 995)

import Mathlib
import Definitions.Def_BasicSolution
import Definitions.Def_Birge1985_Degeneracy_NodeProblem

open Matrix LinearOptimization

namespace Birge1985.Degeneracy

/-- **Birge (1985), Proposition 4, p. 997.** Let `P` be the problem (7) of scenario `j` at
period `t` and `Q j'` (`j' ∈ J'`) the problems (7) of its descendant scenarios at period
`t + 1`, with positive weights `p j'`. Suppose two distinct optimality cuts `l₁ ≠ l₂` of type
(7.4) of `P`, both valid lower bounds on the weighted descendant values (the NDSPA
invariants), are binding at `(xbar, θbar)`. Let each descendant have an optimal basic
feasible solution `z j'` and an optimal dual vector `lam j'` of its problem with `xbar`
input in (7.2), and suppose the completed Step 3a cut `E x + θ ≥ e` built from these duals
does not satisfy (9), i.e. `θbar ≥ e - E xbar`. Then `z j'` is degenerate for some
`j' ∈ J'`. -/
theorem optimality_cuts_force_degeneracy {nIn : ℕ} (P : NodeProblem nIn)
    {J : Type} [Fintype J] (Q : J → NodeProblem P.n) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (l₁ l₂ : Fin P.s) (hdistinct : (P.E l₁, P.e l₁) ≠ (P.E l₂, P.e l₂))
    (hvalid₁ : IsValidOptimalityCut Q p (P.E l₁) (P.e l₁))
    (hvalid₂ : IsValidOptimalityCut Q p (P.E l₂) (P.e l₂))
    (xbar : Fin P.n → ℝ) (θbar : ℝ)
    (hbind₁ : P.E l₁ ⬝ᵥ xbar + θbar = P.e l₁)
    (hbind₂ : P.E l₂ ⬝ᵥ xbar + θbar = P.e l₂)
    (z : ∀ j, Fin ((Q j).n + 1) → ℝ)
    (hbasic : ∀ j, IsBasicFeasibleSolution ((Q j).constraints xbar) (z j))
    (hopt : ∀ j, (Q j).IsOptimalSolution xbar (z j))
    (lam : ∀ j, (Q j).Idx → ℝ)
    (hdual : ∀ j, IsDualOptimal ((Q j).constraints xbar)
      (Fin.snoc (α := fun _ => ℝ) (Q j).c 1) (lam j))
    (hnot9 : optimalityCutConst Q p lam - optimalityCutSlope Q p lam ⬝ᵥ xbar ≤ θbar) :
    ∃ j, IsDegenerateBasicSolution ((Q j).constraints xbar) (z j) := by sorry

end Birge1985.Degeneracy
