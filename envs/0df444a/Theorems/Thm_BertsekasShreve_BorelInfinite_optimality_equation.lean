-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_optimality_equation
-- name    : BertsekasShreve.BorelInfinite.optimality_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:18:45.018391+00:00
-- url     : https://prove2.me/theorems/9b1ea537-45db-4218-9439-6dc54c3c81db
-- title:
--   Proposition 9.8, Eq. (22) — the optimal cost satisfies the optimality equation J* = T(J*) under (P), (N), (D)
-- statement:
--   Let (SM) $= (S, C, U, W, p, f, \alpha, g)$ be an infinite horizon stochastic optimal control model on nonempty Borel spaces that satisfies one of
--
--   - **(P)** $g \ge 0$ on $\Gamma$,
--   - **(N)** $g \le 0$ on $\Gamma$,
--   - **(D)** $0 < \alpha < 1$ and $-b \le g \le b$ on $\Gamma$ for some $b \in \mathbb R$.
--
--   Let $J^*(x) = \inf_{\pi \in \Pi'} J_\pi(x)$ be the optimal cost over all universally measurable, possibly history-dependent and randomized policies. Then $J^*$ satisfies the optimality equation
--   $$J^*(x) = \inf_{u \in U(x)} \Big\{ g(x, u) + \alpha \int_S J^*(x')\, t(dx' \mid x, u) \Big\} \qquad \text{for every } x \in S,$$
--   that is, $J^* = T(J^*)$.
--
--   This is the Bellman equation of infinite horizon dynamic programming on Borel spaces. It holds without any continuity or compactness assumption on the data. Under (P) and (N), the dynamic programming algorithm need not converge to $J^*$, and $J^*$ need not be the only solution of the equation.
--
--   **Formalization Note** $J^*$ is the infimum of the costs of all policies; it is not defined as a fixed point or as a limit of $T^k(0)$. The integral $\int J^* dt$ is the extended integral $\int (J^*)^+ dt - \int (J^*)^- dt$ with $\infty - \infty = \infty$, and the sum $g + \alpha \int J^* dt$ uses the same convention. The statement for the deterministic model (DM) on $P(S)$, Eq. (21), is not formalized.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 225, Proposition 9.8, Eq. (22) of Chapter 9

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.8**, Eq. (22) (p. 225). (P)(N)(D) The optimal cost of (SM) satisfies the
optimality equation `J* = T(J*)`. -/
theorem optimality_equation {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) :
    M.Jstar = M.T M.Jstar := by sorry

end BertsekasShreve.BorelInfinite
