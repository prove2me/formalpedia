-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_prop1_concave
-- name    : FalseFailureReturns.TargetRebate.prop1_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:38:58.155909+00:00
-- url     : https://prove2.me/theorems/fdd06515-9e2c-47cb-8489-7b87fb665cbb
-- title:
--   Proposition 1: if $\partial^2 F(x\mid\rho)/\partial\rho^2 \le 0$, the retailer's rebate profit is concave in $\rho$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ be as in the model, let $u \ge 0$ be the rebate per false failure below the target and $T$ the target. For every effort $\rho \ge 1$ let $X(\rho)$ be a random variable with values in $[0, \infty)$, with law $\mu_\rho$ and cumulative distribution function $F(x \mid \rho) = \mu_\rho((-\infty, x])$. Suppose that for every $x \in [0, T]$ the map $\rho \mapsto F(x \mid \rho)$ is twice continuously differentiable on $[1, \infty)$ with
--   $$\frac{\partial^2 F(x \mid \rho)}{\partial \rho^2} \le 0 \qquad (\rho > 1).$$
--   Then the retailer's expected profit under the target rebate contract,
--   $$\pi_R(\rho \mid T, u) = u\,E\{[T - X(\rho)]^+\} - \frac{a\rho^2}{2} + R_r\,\beta\Big(1 - \frac{1}{\rho}\Big),$$
--   is concave in $\rho$ on $[1, \infty)$.
--
--   Concavity makes the first-order condition sufficient for the retailer's optimal effort, which is how the paper computes coordinating contracts.
--
--   **Formalization Note** The family of laws is an arbitrary map $\rho \mapsto \mu_\rho$ of probability measures on $\mathbb{R}$ with $\mu_\rho((-\infty, 0)) = 0$ for $\rho \ge 1$. The paper's other standing assumptions on $F$ (differentiable and strictly increasing in $x$, $E\{X(\rho)\} = \beta/\rho$) are not imposed: the statement is the proposition under fewer hypotheses, and the paper's version is a special case. The second-derivative condition is required only for $x \in [0, T]$ and only in the interior $\rho > 1$, with twice continuous differentiability on $[1, \infty)$ assumed explicitly so the condition is not vacuous.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 383, Proposition 1

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
open MeasureTheory

namespace FalseFailureReturns.TargetRebate

theorem prop1_concave (P : Params) (μ : ℝ → Measure ℝ) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr) (hu : 0 ≤ u)
    (hprob : ∀ ρ ∈ Set.Ici (1 : ℝ), IsProbabilityMeasure (μ ρ))
    (hnonneg : ∀ ρ ∈ Set.Ici (1 : ℝ), μ ρ (Set.Iio 0) = 0)
    (hF_smooth : ∀ x ∈ Set.Icc 0 T,
      ContDiffOn ℝ 2 (fun ρ => (μ ρ (Set.Iic x)).toReal) (Set.Ici 1))
    (hF_second : ∀ x ∈ Set.Icc 0 T, ∀ ρ ∈ Set.Ioi (1 : ℝ),
      deriv (deriv (fun ρ => (μ ρ (Set.Iic x)).toReal)) ρ ≤ 0) :
    ConcaveOn ℝ (Set.Ici 1)
      (fun ρ => u * ∫ x, max (T - x) 0 ∂(μ ρ) - P.a * ρ ^ 2 / 2 + P.Rr * P.β * (1 - 1 / ρ)) := by sorry

end FalseFailureReturns.TargetRebate
