-- Prove2me | Theorems.Thm_DebtDoubleMarg_thresholds_coincide
-- name    : DebtDoubleMarg.thresholds_coincide
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:50.411583+00:00
-- url     : https://prove2.me/theorems/f9b1e54f-600a-4f62-8205-91297305272b
-- title:
--   §3.1 — the thresholds coincide: $\tilde X_F=\tilde X_D=\frac{\beta_1+1}{\beta_1-1}\delta(r-\mu)$
-- statement:
--   Assume the standing assumptions and let the demand be driven by a standard Brownian motion. Write $d=\delta(r-\mu)$, $X^*_F=\frac{\beta_1+1}{\beta_1-1}d$, and, for an initial level $x_0$ and a threshold $X_F$,
--   $$f_F(x_0,X_F)=\mathbb E\big[e^{-r\tilde\tau(X_F;x_0)}\big]J_F\big(X_F,\rho^{imm}(X_F)\big),\qquad f_D(x_0,X_F)=\mathbb E\big[e^{-r\tilde\tau(X_F;x_0)}\big]J_D\big(X_F,\rho^{imm}(X_F)\big),$$
--   the firm's and the lender's timing payoffs when the coupon is $\rho^{imm}$ at every level.
--
--   1. For every $0<x_0<X^*_F$ and every $X_F\ge x_0$ with $X_F\ne X^*_F$: $f_F(x_0,X_F)<f_F(x_0,X^*_F)$ and $f_D(x_0,X_F)<f_D(x_0,X^*_F)$. So the firm's threshold $\tilde X_F$ and the lender's threshold $\tilde X_D$ both equal $X^*_F$.
--   2. For every $x_0\ge X^*_F$ and every $X_F>x_0$: $f_F(x_0,X_F)<J_F(x_0,\rho^{imm}(x_0))$ and $f_D(x_0,X_F)<J_D(x_0,\rho^{imm}(x_0))$, so investing at once is strictly best for both.
--
--   This is the key step of the proof of Proposition 1 as described on p.8: because the two thresholds coincide, the lender can offer $\rho^{imm}$ above $X^*_F$ and an infinite coupon below it.
--
--   Differences from the source:
--   - reading: "the two investment thresholds X̃D and X̃F of the lender and the firm coincide" (X̃F, X̃D defined in §3, p.7) → for 0 < x₀ < X*_F, X*_F = (β₁ + 1)/(β₁ − 1)·δ(r − µ) is the unique maximizer over X_F ≥ x₀ of both timing payoffs under ρ^imm; for x₀ ≥ X*_F every X_F > x₀ is strictly worse than immediate investment for both; reason: X̃F and X̃D are the thresholds of the firm's and the lender's timing problems under ρ^imm; the common value X*_F = X̃D is the p.8 sentence
--   - encoding: the firm's stopping region [X_F, ∞) (p.6, endnote 6) → the firm chooses a threshold X_F ≥ 0; it waits if x₀ < X_F and invests at once otherwise; reason: the paper's own restriction to threshold strategies
--   - encoding: J_D(X, ρ) = E₀{∫₀^∞ ρδI* e^{−rt}dt − δI*} ((3) with τ_B = ∞) → the same expression without E₀; reason: the integrand is deterministic once X and ρ are fixed, so the expectation under a probability measure is the expression itself
--   - encoding: no bankruptcy option (§3.1): the firm pays coupons perpetually → bankruptcy time τ_B = ∞: integrals over (0, ∞), no bankruptcy term, no α; reason: this is the scenario of Proposition 1
--   - encoding: dx(t) = µx(t)dt + σx(t)dω(t), x(0) = X (p.4) → x(t) = X·exp((µ − σ²/2)t + σW_t) for a Mathlib Brownian motion W (IsBrownianReal), on any probability space; reason: the unique strong solution of the SDE; the statement holds for every probability space carrying a Brownian motion
--   - encoding: σ and r not restricted beyond r > µ, δ called "the unit investment cost" (p.4) → hypotheses σ > 0, r > 0 and δ > 0 (in Params.Standing); reason: r > 0 makes ∫₀^∞ e^{−rt}dt finite and σ ≠ 0 makes the quadratic defining β₁ have two roots; σ > 0 is the volatility convention; δ > 0 is the positivity of a cost and (6) divides by δ(r − µ); only undefined or degenerate cases are excluded
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, §3.1 p.8 (paragraph after Proposition 1); X̃F, X̃D defined in §3 p.7. Proof step of Proposition 1

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM
import Definitions.Def_DebtDoubleMarg_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **The firm's and the lender's thresholds under `ρ^imm` coincide.** Under the standing
assumptions, for a standard Brownian motion `W`, with `X̃ = X*_F = (β₁ + 1)/(β₁ − 1) · δ(r − µ)`,
`f_F(x₀, X_F) = E[e^{−rτ̃(X_F; x₀)}] · J_F(X_F, ρ^imm(X_F))` (the firm's timing payoff under
`ρ^imm`) and `f_D(x₀, X_F) = E[e^{−rτ̃(X_F; x₀)}] · J_D(X_F, ρ^imm(X_F))` (the lender's):
1. for `0 < x₀ < X̃`, `X̃` is the unique maximizer of `f_F(x₀, ·)` and of `f_D(x₀, ·)` over
   `X_F ≥ x₀` (so `X̃_F = X̃_D = X̃`);
2. for `x₀ ≥ X̃`, every `X_F > x₀` gives strictly less than investing at `x₀`, for the firm
   (`J_F(x₀, ρ^imm(x₀))`) and for the lender (`J_D(x₀, ρ^imm(x₀))`).

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §3.1, p.8 ("the two
investment thresholds X̃D and X̃F of the lender and the firm coincide"), with `X̃_F`, `X̃_D`
defined in §3, p.7. A proof step of Proposition 1. -/
theorem thresholds_coincide (p : Params) (hp : p.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) :
    (∀ x0 : ℝ, 0 < x0 → x0 < nboTrigger p → ∀ XF : ℝ, x0 ≤ XF → XF ≠ nboTrigger p →
        expectedPassageDiscount p.μ p.σ p.r P W XF x0 * firmValue p P W XF (immCoupon p XF) <
          expectedPassageDiscount p.μ p.σ p.r P W (nboTrigger p) x0 *
            firmValue p P W (nboTrigger p) (immCoupon p (nboTrigger p)) ∧
        expectedPassageDiscount p.μ p.σ p.r P W XF x0 * lenderValue p P W XF (immCoupon p XF) <
          expectedPassageDiscount p.μ p.σ p.r P W (nboTrigger p) x0 *
            lenderValue p P W (nboTrigger p) (immCoupon p (nboTrigger p))) ∧
      (∀ x0 : ℝ, nboTrigger p ≤ x0 → ∀ XF : ℝ, x0 < XF →
        expectedPassageDiscount p.μ p.σ p.r P W XF x0 * firmValue p P W XF (immCoupon p XF) <
            firmValue p P W x0 (immCoupon p x0) ∧
        expectedPassageDiscount p.μ p.σ p.r P W XF x0 * lenderValue p P W XF (immCoupon p XF) <
            lenderValue p P W x0 (immCoupon p x0)) := by sorry

end DebtDoubleMarg
