-- Prove2me | Theorems.Thm_DirectTradeCoffee_proposition_A1
-- name    : DirectTradeCoffee.proposition_A1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:20.332809+00:00
-- url     : https://prove2.me/theorems/771764f8-4803-4003-9d11-ad7de2d9b11a
-- title:
--   Proposition A1, p.33 — $\Pi$ is concave on $[0,\infty)$ and strictly concave on $[0,Q_H]$ (corrected: $\Pi+k$ is affine on $[Q_H,\infty)$)
-- statement:
--   The expected profit $\Pi$ is concave on $[0,\infty)$ and strictly concave on $[0,Q_H]$. On $[Q_H,\infty)$ every realization is unconstrained and
--
--   $$
--   \Pi(Q) + k(Q) = \frac1b\,E\big[W(x(\tilde\varphi))\big] + (\mu_\varphi + \rho\sigma_\varphi\sigma_y - c)\,Q ,
--   \qquad x(\varphi) = \frac{e^{v-1}}{e^{b\varphi}+e^{v_B}} .
--   $$
--
--   Concavity makes the first-order conditions at $Q_L$ and $Q_H$ decide the optimal strategy, and strictness on $[0,Q_H]$ makes the strategy class of an optimal acreage unique under uncertainty.
--
--   Differences from the source:
--   - correction: Π is strictly concave on [0, ∞) → Π is concave on [0, ∞), strictly concave on [0, Q_H], and Π + k is affine on [Q_H, ∞) with the displayed formula; reason: on [Q_H, ∞) every realization is unconstrained, so Π is affine when k is; counterexample: b = 1, v = 20, v_B = 17, c = 13.25, Ω = [13, 17] × [0.5, 1.5], independent uniform laws and k(Q) = 1.75 Q give Π(Q_H) = Π(Q_H + 1) = 1.43839
--   - generalization: v > v_B (p.9; p.31 prints v_B > v) → no order between v and v_B is assumed; reason: no step uses it, and p.9 and p.31 disagree; every instance of the paper is covered
--   - reading: p.13 illustrates a capacity limit Q_max by k′(Q_max) = ∞ → k is real-valued and continuous on [0, ∞), as p.10 and p.31 assume; reason: the illustration lies outside the model assumption that k is a continuous function; every k of the model is covered
--   - encoding: second-stage constraint 0 ≤ q ≤ 1 → 0 ≤ q < 1; reason: at q = 1 no finite price clears the market and the objective tends to −∞; the maximum and its maximizer are unchanged
--   - encoding: F has support Ω → F(Ωᶜ) = 0 and every open ball around a point of Ω has positive mass; reason: this is the definition of the support of a measure
--   - encoding: μ_φ + ρσ_φσ_y → U.meanφ + U.cov, with the covariance ∫(φ − μ_φ)(y − 1) dF; reason: ρ is undefined when a variance is 0; the two agree whenever ρ is defined
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, Proposition A1, p.33; proof pp.33–34

import Mathlib
import Definitions.Def_DirectTradeCoffee_Model

open MeasureTheory

namespace DirectTradeCoffee

/-- **Proposition A1** (corrected), Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for
Specialty Coffee*, MSOM (2024), doi:10.1287/msom.2021.0586, p.33: `Π` is concave on `[0, ∞)`,
strictly concave on `[0, Q_H]`, and `Π + k` is affine on `[Q_H, ∞)`, with
`Π(Q) + k(Q) = E[W(x(φ̃))]/b + (μ_φ + ρσ_φσ_y − c) Q` there.

**Formalization Note.** The printed statement is "strictly concave on `[0, ∞)`", which fails for
affine `k`, because every realization is unconstrained on `[Q_H, ∞)`. -/
theorem proposition_A1 (P : Params) {k : ℝ → ℝ} (hk : IsCost k) (U : Uncertainty) :
    ConcaveOn ℝ (Set.Ici 0) (expectedProfit P k U) ∧
    StrictConcaveOn ℝ (Set.Icc 0 (QH P U)) (expectedProfit P k U) ∧
    ∀ Q, QH P U ≤ Q →
      expectedProfit P k U Q + k Q =
        (∫ z, lambertW (xArg P z.1) ∂U.F) / P.b + (U.meanφ + U.cov - P.c) * Q := by sorry

end DirectTradeCoffee
