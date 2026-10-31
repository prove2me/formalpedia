-- Prove2me | Theorems.Thm_DebtDoubleMarg_lender_immediate_coupon
-- name    : DebtDoubleMarg.lender_immediate_coupon
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:48.618378+00:00
-- url     : https://prove2.me/theorems/445d8cd8-2e9e-4a14-8ea0-a70bddde4aaa
-- title:
--   (9) without bankruptcy — the lender's immediate-investment coupon $\rho^{imm}(X)=\frac{r(X+\delta(r-\mu))}{2\delta(r-\mu)}$
-- statement:
--   Assume the standing assumptions and let the demand be driven by a standard Brownian motion. Write $d=\delta(r-\mu)$ and $\rho^{imm}(X)=\dfrac{r(X+d)}{2d}$.
--
--   1. For every $X>d$, $\rho^{imm}(X)$ is the unique maximizer of the lender's NPV $J_D(X,\cdot)$ over $\rho\ge0$, and
--   $$J_D\big(X,\rho^{imm}(X)\big)=\frac{\delta(X-d)^2}{8\eta dX}.$$
--   2. For every $0<X\le d$ and every $\rho\ge0$, $J_D(X,\rho)\le0$.
--
--   This is the coupon (9) of the paper, which maximizes the lender's value when the firm invests immediately, in the scenario without bankruptcy. It is a step of the proof of Proposition 1.
--
--   Differences from the source:
--   - encoding: (9): J_D with the bankruptcy term (ρδI∗/r)·(1 − αβ2)/(1 − β2)·(X/X∗_B)^β2 → J_D(X, ρ) = ∫₀^∞ ρδI∗e^{−rt}dt − δI∗, no bankruptcy term; reason: without a bankruptcy option τ_B = ∞ and the term vanishes
--   - reading: ρimm(X) = arg sup_{ρ≥0} JD(X, ρ) for each X → for X > δ(r − µ) the unique maximizer is r(X + δ(r − µ))/(2δ(r − µ)) with value δ(X − δ(r − µ))²/(8ηδ(r − µ)X); for 0 < X ≤ δ(r − µ), J_D(X, ρ) ≤ 0 for all ρ ≥ 0; reason: for X ≤ δ(r − µ), I∗ = 0 for every ρ ≥ rX/(δ(r − µ)), so J_D(X, ·) vanishes on an interval and has no unique maximizer
--   - encoding: J_D(X, ρ) = E₀{∫₀^∞ ρδI* e^{−rt}dt − δI*} ((3) with τ_B = ∞) → the same expression without E₀; reason: the integrand is deterministic once X and ρ are fixed, so the expectation under a probability measure is the expression itself
--   - encoding: dx(t) = µx(t)dt + σx(t)dω(t), x(0) = X (p.4) → x(t) = X·exp((µ − σ²/2)t + σW_t) for a Mathlib Brownian motion W (IsBrownianReal), on any probability space; reason: the unique strong solution of the SDE; the statement holds for every probability space carrying a Brownian motion
--   - encoding: σ and r not restricted beyond r > µ, δ called "the unit investment cost" (p.4) → hypotheses σ > 0, r > 0 and δ > 0 (in Params.Standing); reason: r > 0 makes ∫₀^∞ e^{−rt}dt finite and σ ≠ 0 makes the quadratic defining β₁ have two roots; σ > 0 is the volatility convention; δ > 0 is the positivity of a cost and (6) divides by δ(r − µ); only undefined or degenerate cases are excluded
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, (9) p.10, without the bankruptcy term. Proof step of Proposition 1

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM
import Definitions.Def_DebtDoubleMarg_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **The lender's immediate-investment coupon.** Under the standing assumptions, for a standard
Brownian motion `W`, with `d = δ(r − µ)`:
1. for `X > d`, `ρ^imm(X) = r(X + d)/(2d)` is the unique maximizer of `J_D(X, ·)` on `ρ ≥ 0`,
   and `J_D(X, ρ^imm(X)) = δ(X − d)² / (8ηdX)`;
2. for `0 < X ≤ d`, `J_D(X, ρ) ≤ 0` for every `ρ ≥ 0`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (9), p.10, without the
bankruptcy term (`τ_B = ∞`). A proof step of Proposition 1. -/
theorem lender_immediate_coupon (p : Params) (hp : p.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) :
    (∀ X : ℝ, p.δ * (p.r - p.μ) < X →
        (∀ ρ : ℝ, 0 ≤ ρ → ρ ≠ immCoupon p X →
          lenderValue p P W X ρ < lenderValue p P W X (immCoupon p X)) ∧
        lenderValue p P W X (immCoupon p X) =
          p.δ * (X - p.δ * (p.r - p.μ)) ^ 2 / (8 * p.η * (p.δ * (p.r - p.μ)) * X)) ∧
      (∀ X : ℝ, 0 < X → X ≤ p.δ * (p.r - p.μ) → ∀ ρ : ℝ, 0 ≤ ρ →
        lenderValue p P W X ρ ≤ 0) := by sorry

end DebtDoubleMarg
