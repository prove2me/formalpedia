-- Prove2me | Theorems.Thm_DebtDoubleMarg_lender_value_le_immediate
-- name    : DebtDoubleMarg.lender_value_le_immediate
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:56.702253+00:00
-- url     : https://prove2.me/theorems/789a5e86-8423-4abe-8f2e-4d1b7bbb56bc
-- title:
--   §3 — time consistency: the lender's payoff is at most its payoff under $\rho^{imm}$ at the same investment level
-- statement:
--   Assume the standing assumptions and let the demand be driven by a standard Brownian motion. For every initial demand level $x_0>0$, every coupon scheme $\rho$ with values in $[0,\infty]$ and every threshold $X_F\ge0$,
--   $$V_D(x_0;\rho,X_F)\le\begin{cases}\mathbb E\big[e^{-r\tilde\tau(X_F;x_0)}\big]\,J_D\big(X_F,\rho^{imm}(X_F)\big) & x_0<X_F,\\ J_D\big(x_0,\rho^{imm}(x_0)\big) & \text{otherwise.}\end{cases}$$
--
--   This is the first observation of §3: whenever the lender induces investment, its value cannot exceed what the coupon $\rho^{imm}$ yields at that level, so the lender's problem reduces to a timing problem under $\rho^{imm}$. It is a step of the proof of Proposition 1.
--
--   Differences from the source:
--   - generalization: for X at which the lender induces investment, ρ∗(X) must maximize JD(X, ρ∗(X)) under the constraint that it is optimal for the firm to invest at X → for every x₀ > 0, every scheme ρ and every threshold X_F ≥ 0 (firm-optimal or not), V_D(x₀; ρ, X_F) is at most the same payoff with ρ(X_F) (resp. ρ(x₀)) replaced by ρ^imm; reason: dropping the firm-optimality constraint only enlarges the set of (scheme, threshold) pairs, so the bound specializes to the paper's
--   - encoding: the firm's stopping region [X_F, ∞) (p.6, endnote 6) → the firm chooses a threshold X_F ≥ 0; it waits if x₀ < X_F and invests at once otherwise; reason: the paper's own restriction to threshold strategies
--   - encoding: ρ(X) = ∞ (financing refused) → WithTop ℝ with ⊤, and J_F(X, ⊤) = J_D(X, ⊤) = 0; reason: at an infinite coupon nothing is invested and no cash flows occur
--   - encoding: J_D(X, ρ) = E₀{∫₀^∞ ρδI* e^{−rt}dt − δI*} ((3) with τ_B = ∞) → the same expression without E₀; reason: the integrand is deterministic once X and ρ are fixed, so the expectation under a probability measure is the expression itself
--   - encoding: no bankruptcy option (§3.1): the firm pays coupons perpetually → bankruptcy time τ_B = ∞: integrals over (0, ∞), no bankruptcy term, no α; reason: this is the scenario of Proposition 1
--   - encoding: dx(t) = µx(t)dt + σx(t)dω(t), x(0) = X (p.4) → x(t) = X·exp((µ − σ²/2)t + σW_t) for a Mathlib Brownian motion W (IsBrownianReal), on any probability space; reason: the unique strong solution of the SDE; the statement holds for every probability space carrying a Brownian motion
--   - encoding: σ and r not restricted beyond r > µ, δ called "the unit investment cost" (p.4) → hypotheses σ > 0, r > 0 and δ > 0 (in Params.Standing); reason: r > 0 makes ∫₀^∞ e^{−rt}dt finite and σ ≠ 0 makes the quadratic defining β₁ have two roots; σ > 0 is the volatility convention; δ > 0 is the positivity of a cost and (6) divides by δ(r − µ); only undefined or degenerate cases are excluded
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, §3 p.7 (first observation). Proof step of Proposition 1

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM
import Definitions.Def_DebtDoubleMarg_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **Time-consistency reduction.** Under the standing assumptions, for a standard Brownian
motion `W`, every initial level `x₀ > 0`, every coupon scheme `ρ` and every threshold
`X_F ≥ 0`, the lender's payoff is at most its payoff when the coupon at the investment level is
replaced by `ρ^imm`:
`V_D(x₀; ρ, X_F) ≤ E[e^{−rτ̃(X_F; x₀)}] · J_D(X_F, ρ^imm(X_F))` if `x₀ < X_F`, and
`V_D(x₀; ρ, X_F) ≤ J_D(x₀, ρ^imm(x₀))` otherwise.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §3, p.7 (first
observation: "ρ∗(X) must maximize JD(X, ρ∗(X))"). A proof step of Proposition 1.

**Formalization Note** The bound holds for every threshold, firm-optimal or not. -/
theorem lender_value_le_immediate (p : Params) (hp : p.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (x0 : ℝ) (hx0 : 0 < x0) (ρ : ℝ → WithTop ℝ)
    (hρ : IsCouponScheme ρ) (XF : ℝ) (hXF : 0 ≤ XF) :
    lenderPayoff p P W ρ x0 XF ≤
      if x0 < XF then
        expectedPassageDiscount p.μ p.σ p.r P W XF x0 * lenderValue p P W XF (immCoupon p XF)
      else lenderValue p P W x0 (immCoupon p x0) := by sorry

end DebtDoubleMarg
