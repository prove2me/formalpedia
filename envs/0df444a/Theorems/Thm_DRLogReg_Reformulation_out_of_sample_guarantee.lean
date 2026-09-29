-- Prove2me | Theorems.Thm_DRLogReg_Reformulation_out_of_sample_guarantee
-- name    : DRLogReg.Reformulation.out_of_sample_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:36:32.247245+00:00
-- url     : https://prove2.me/theorems/c80a61ac-d48e-4747-873f-0cda37ee0044
-- title:
--   Theorem 2, "implying" clause — if P lies in the Wasserstein ball, the out-of-sample logloss of β̂ is at most Ĵ
-- statement:
--   Let $V$ be a finite-dimensional real normed space with any norm, $\kappa>0$, $\varepsilon\ge0$, $N\ge1$, and let $\mathbb P$ be a probability distribution on $\Xi = V\times\{-1,+1\}$. Draw the training set $\hat\Xi_N = \{(\hat x_i,\hat y_i)\}_{i=1}^N$ independently from $\mathbb P$, i.e. with law $\mathbb P^N$. For every training set let $(\hat\beta,\hat\lambda,\hat s)$ be an optimal solution of program (7) built from it, with optimal value $\hat J$. Let $\eta\in(0,1]$. If
--   $$\mathbb P^N\big\{\mathbb P\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)\big\}\ge 1-\eta,$$
--   then
--   $$\mathbb P^N\big\{\hat\Xi_N : \mathbb E^{\mathbb P}\big[l_{\hat\beta}(x,y)\big]\le\hat J\big\}\ge1-\eta.$$
--
--   That is, whenever the Wasserstein ball contains the data-generating distribution with confidence $1-\eta$, the optimal value $\hat J$ of (7) is an upper confidence bound, at the same level, on the out-of-sample logloss of the robust classifier $\hat\beta$.
--
--   The first claim of Theorem 2, that the radius $\varepsilon_N(\eta)$ of eq. (8) guarantees $\mathbb P^N\{\mathbb P\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)\}\ge1-\eta$ for light-tailed $\mathbb P$, is a measure-concentration result and is not part of this statement: the confidence bound on the ball event is a hypothesis here.
--
--   **Formalization Note.** $\mathbb P^N$ is the product measure on $(V\times\{-1,+1\})^N$; probabilities of events are its outer measure, so no measurability of the events is assumed. The optimal solution is a function `sol` of the training set that is required to be optimal for every training set. Expectations are lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 4, Theorem 2 ("implying" clause)

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

/-- Theorem 2, "implying" clause (Out-of-Sample Performance), Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally Robust Logistic Regression*,
NIPS 2015, p. 4.

Let `P` be a probability distribution on `Ξ` and let the `N` training samples be drawn
independently from `P` (law `P^N`). Let `sol` assign to every training set an optimal solution
`(β̂, λ̂, ŝ)` of program (7), so that `Ĵ = objective7 ε (sol ω)` is its optimal value. If
`P^N{P ∈ B_ε(P̂_N)} ≥ 1 − η` for a confidence level `η ∈ (0, 1]`, then
`P^N{Ξ̂_N : E^P[l_β̂(x, y)] ≤ Ĵ} ≥ 1 − η`. The first claim of Theorem 2 (the choice (8) of `ε`
achieving `P^N{P ∈ B_ε(P̂_N)} ≥ 1 − η` under a light-tail assumption) is not formalized; the
event bound is a hypothesis here. -/
theorem out_of_sample_guarantee
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (P : Measure (V × Bool)) [IsProbabilityMeasure P]
    (sol : (Fin N → V × Bool) → (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ))
    (hsol : ∀ ω : Fin N → V × Bool,
      sol ω ∈ feasible7 κ (fun i => (ω i).1) (fun i => (ω i).2) ∧
        ∀ q ∈ feasible7 κ (fun i => (ω i).1) (fun i => (ω i).2),
          objective7 ε (sol ω) ≤ objective7 ε q)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hconf : ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ω | P ∈ wassersteinBall κ ε (empirical (fun i => (ω i).1) (fun i => (ω i).2))}) :
    ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ω | ∫⁻ ξ, ENNReal.ofReal (logloss (sol ω).1 ξ.1 ξ.2) ∂P ≤
        ENNReal.ofReal (objective7 ε (sol ω))} := by sorry

end DRLogReg.Reformulation
