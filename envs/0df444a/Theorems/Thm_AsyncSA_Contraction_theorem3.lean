-- Prove2me | Theorems.Thm_AsyncSA_Contraction_theorem3
-- name    : AsyncSA.Contraction.theorem3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:00.254088+00:00
-- url     : https://prove2.me/theorems/080c9ec7-426f-40fe-a908-9d29bd3b31f3
-- title:
--   Theorem 3 — almost-sure convergence under a weighted maximum norm contraction
-- statement:
--   Consider the asynchronous stochastic approximation iteration of §2 under Assumptions 1, 2, and 3. Suppose Assumption 5 holds: there are a vector $x^*\in\mathbb R^n$, a strictly positive weight vector $v$, and $\beta\in[0,1)$ such that
--
--   $$\|F(y)-x^*\|_v\le\beta\|y-x^*\|_v\qquad\text{for every }y\in\mathbb R^n.$$
--
--   Then $x(t)\to x^*$ with probability one, including when different coordinates are updated at different times using outdated values.
--
--   This is the paper's contraction-based convergence theorem and the mission's goal.
--
--   **Formalization Note** The witnesses $x^*$, $v$, and $\beta$ are explicit binders, equivalent to their existence in Assumption 5. The paper implicitly treats $x(t)$ as adapted to $\mathcal F(t)$; the statement includes adaptedness. No separate boundedness or Assumption 6 hypothesis is made.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 189, §2, Theorem 3; proof pp. 195–196, §6

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

namespace AsyncSA.Contraction

open MeasureTheory Filter Topology

/-- Theorem 3, p. 189: almost-sure convergence to the contraction's fixed point. -/
theorem theorem3 {n : ℕ} {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (alg : Algorithm n Ω)
    (xstar v : Fin n → ℝ) (β : ℝ)
    (h1 : alg.Assumption1 P) (h2 : alg.Assumption2 P 𝓕)
    (hx : alg.Adapted 𝓕) (h3 : alg.Assumption3 P)
    (h5 : Assumption5 alg.F xstar v β) :
    ∀ᵐ ω ∂P, Tendsto (fun t => alg.x t ω) atTop (𝓝 xstar) := by sorry

end AsyncSA.Contraction
