-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_eq_3_3
-- name    : FiniteMemQL.Convergence.eq_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:53.445655+00:00
-- url     : https://prove2.me/theorems/ef4543e7-9ba2-4e22-8d71-a9e1be6af8af
-- title:
--   (3.3), p. 9 — the discounted cost optimality equation of the finite-window belief MDP
-- statement:
--   Let $\pi$ be a probability measure on $\mathbb X$ (the prior of the state at the oldest time of the window) and $I$ a window. The optimal value of the finite-window belief MDP satisfies
--   $$
--   J^*_\beta(\pi,I)=\min_{u\in\mathbb U}\Bigl(\hat c(\pi,I,u)+\beta\sum_{y\in\mathbb Y}J^*_\beta\bigl(G(\pi,I,u),\mathrm{shift}(I,u,y)\bigr)\,P^{\pi}(y\mid I,u)\Bigr),
--   $$
--   where $G(\pi,I,u)$ is the predictor one step later and $\mathrm{shift}(I,u,y)$ the next window. For $N=1$ and $I=(y_1,y_0,u_0)$ this is the paper's (3.3). It is the equation the proof of Theorem 3.2 compares with the approximate model's equation (3.8).
--
--   **Formalization Note** $J^*_\beta(\pi,I)$ is the belief-MDP value at $\psi(\pi,I)$. On windows of probability zero both sides are $0$.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 9, §3.1, (3.3)

import Mathlib
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- (3.3), p. 9 (arXiv:2103.12158v4): the discounted cost optimality equation of the finite-window
belief MDP. For every prior `π` of the state at the oldest time of the window `I`,
`J*_β(π, I) = min_u ( ĉ(π, I, u) + β Σ_y P^π(y | I, u) J*_β(G(π, I, u), shift(I, u, y)) )`. -/
theorem eq_3_3 {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (π : Measure X) [IsProbabilityMeasure π] (I : Window Y U N) :
    JstarW M π I = ⨅ u : U, (chat M π I u +
      M.β * ∑ y : Y, predY M π I u y * JstarW M (nextPrior M π I u) (shift I u y)) := by sorry

end FiniteMemQL.Convergence
