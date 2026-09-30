-- Prove2me | Theorems.Thm_Birge1985_Degeneracy_feasibility_cut_forces_degeneracy
-- name    : Birge1985.Degeneracy.feasibility_cut_forces_degeneracy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:31:53.916961+00:00
-- url     : https://prove2.me/theorems/1432c1fb-f962-41d5-94f1-70e397f21cf6
-- title:
--   Proposition 3 — a binding feasibility cut makes every basic feasible solution of the generating descendant degenerate
-- statement:
--   This is Proposition 3 of Birge (1985) on the degeneracy of nested decomposition.
--
--   Let $P$ be the scenario problem (7) of scenario $j$ at period $t$, with decision $x \in \mathbb{R}^{n}$, and let $Q$ be the problem (7) of a descendant scenario $j'$ at period $t+1$, whose right-hand side in (7.2) is $\xi' + B' x$. Suppose that $j'$ **generates** the feasibility cut $l'$ of type (7.3) of $P$: there is an ancestor decision $x^0$ at which $Q$ is infeasible, a Farkas certificate $\lambda$ of that infeasibility for the constraint family of $Q$ at $x^0$, and row $l'$ of (7.3) in $P$ is
--
--   $$
--   D_{l'}^\top x \ge d_{l'}, \qquad D_{l'} = -\pi^\top B', \quad d_{l'} = \pi^\top \xi' + \rho^\top d' + \sigma^\top e',
--   $$
--
--   where $\pi, \rho, \sigma$ are the parts of $\lambda$ on the rows (7.2), (7.3), (7.4) of $Q$. If the cut is binding at a point $\bar x$, that is $D_{l'}^\top \bar x = d_{l'}$, then
--
--   $$
--   \text{every basic feasible solution of } Q \text{ with } \bar x \text{ input in (7.2) is degenerate.}
--   $$
--
--   Here "basic feasible" and "degenerate" are the general-form notions for the whole constraint family of (7), the free variable $\theta$ included: a basic feasible solution is degenerate when more than $n' + 1$ constraints are active at it, $n'$ being the dimension of the descendant's decision.
--
--   The proposition explains one source of the repeated solutions observed in NDSPA (Remark 4 of the paper): once the ancestor settles on a point where a feasibility cut binds, the descendant that produced the cut can only answer with degenerate bases. The paper states it and refers its proof to Birge (1980).
--
--   **Formalization Note.** The paper writes "generate a feasibility constraint"; this statement reads it as the Van Slyke–Wets construction from a Farkas certificate, stated against the descendant's *current* constraint family (a certificate for the smaller family it had when the cut was generated extends by zeros, so this hypothesis is the more general one). "Binding for some solution $\bar x$ of (7)" is read as: row $l'$ holds with equality at $\bar x$; feasibility or optimality of $\bar x$ for $P$ is not required, which only strengthens the statement. When $Q$ is infeasible at $\bar x$ the conclusion holds vacuously, as it does in the paper. No rank assumption on the descendant's matrix is added: under the general-form definition, redundant equality rows already make every basic solution degenerate.
-- source:
--   Birge, Decomposition and Partitioning Methods for Multistage Stochastic Linear Programs, Operations Research 33(5), 1985, p. 997, Proposition 3

import Mathlib
import Definitions.Def_BasicSolution
import Definitions.Def_Birge1985_Degeneracy_NodeProblem

open Matrix LinearOptimization

namespace Birge1985.Degeneracy

/-- **Birge (1985), Proposition 3, p. 997.** Let the descendant problem `Q` (scenario `j'`
at period `t + 1`) generate the feasibility cut `l'` of type (7.3) of the ancestor problem
`P` (scenario `j` at period `t`): `Q` is infeasible at an earlier ancestor decision `x0`,
`lam` is a Farkas certificate of that, and row `l'` of (7.3) is `D x ≥ d` with
`D = -π B`, `d = π ξ + ρ d_Q + σ e_Q`. If row `l'` is binding at `xbar`, then every basic
feasible solution of `Q`'s problem (7) with `xbar` input in (7.2) is degenerate. -/
theorem feasibility_cut_forces_degeneracy {nIn : ℕ} (P : NodeProblem nIn)
    (Q : NodeProblem P.n) (x0 : Fin P.n → ℝ) (lam : Q.Idx → ℝ) (l' : Fin P.r)
    (hgen : IsGeneratedFeasibilityCut Q x0 lam (P.D l') (P.d l'))
    (xbar : Fin P.n → ℝ) (hbind : P.D l' ⬝ᵥ xbar = P.d l') :
    ∀ z : Fin (Q.n + 1) → ℝ, IsBasicFeasibleSolution (Q.constraints xbar) z →
      IsDegenerateBasicSolution (Q.constraints xbar) z := by sorry

end Birge1985.Degeneracy
