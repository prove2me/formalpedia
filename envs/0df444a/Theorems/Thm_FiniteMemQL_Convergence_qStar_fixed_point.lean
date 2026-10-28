-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_qStar_fixed_point
-- name    : FiniteMemQL.Convergence.qStar_fixed_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:53.564811+00:00
-- url     : https://prove2.me/theorems/45dcea83-e85c-4b53-aa94-af182164e2e6
-- title:
--   (4.5)–(4.6), p. 15 — Q* solves the fixed point equation of the approximate finite-window model
-- statement:
--   Let $\pi^*$ be a probability measure on $\mathbb X$. The Q-function $Q^*$ of the approximate model with predictor $\pi^*$ satisfies, for every window $I$ and action $u$,
--   $$
--   Q^*(I,u)=C^*(I,u)+\beta\sum_{y\in\mathbb Y}P^{\pi^*}(y\mid I,u)\,\min_{v\in\mathbb U}Q^*\bigl(\mathrm{shift}(I,u,y),v\bigr),
--   $$
--   which is (4.5) written with the transition weights (4.2)–(4.3); for $N=1$ it is (4.6). This is the limit the Q-learning iterates of (4.1) are shown to converge to.
--
--   **Formalization Note** $Q^*$ is defined as the limit of Q-value iteration from $0$; the statement asserts that this limit solves (4.5).
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 15, §4, (4.5)–(4.6)

import Mathlib
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- (4.5)–(4.6), p. 15 (arXiv:2103.12158v4): `Q*` (the limit of Q-value iteration for the
approximate model with predictor `π*`) solves the fixed point equation
`Q*(I, u) = C*(I, u) + β Σ_{I'} P*(I' | I, u) min_v Q*(I', v)`. -/
theorem qStar_fixed_point {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (πs : Measure X) [IsProbabilityMeasure πs] :
    ∀ (I : Window Y U N) (u : U), qStar M πs I u =
      Cstar M πs I u + M.β * ∑ y : Y, Pstar M πs I u y * ⨅ v : U, qStar M πs (shift I u y) v := by sorry

end FiniteMemQL.Convergence
