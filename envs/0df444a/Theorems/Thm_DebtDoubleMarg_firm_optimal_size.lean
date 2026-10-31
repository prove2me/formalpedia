-- Prove2me | Theorems.Thm_DebtDoubleMarg_firm_optimal_size
-- name    : DebtDoubleMarg.firm_optimal_size
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:55.788009+00:00
-- url     : https://prove2.me/theorems/e369c48b-9b9c-42df-8a72-3d232fd716e3
-- title:
--   §2.3 — the firm's optimal capacity $I^*(X,\rho)=\max\{0,\frac1{2\eta}(1-\frac{\rho\delta(r-\mu)}{rX})\}$ and value $J_F(X,\rho)$
-- statement:
--   Assume the standing assumptions and let the demand be driven by a standard Brownian motion. Fix an investment level $X>0$ and a finite coupon rate $\rho\ge0$, and write $d=\delta(r-\mu)$. Then:
--
--   1. $I_0=\max\Big\{0,\ \dfrac1{2\eta}\Big(1-\dfrac{\rho d}{rX}\Big)\Big\}$ maximizes $\tilde J_F(X,\rho,\cdot)$ over $I\ge0$;
--   2. if $\rho>0$, $I_0$ is the only maximizer;
--   3. the firm's value is
--   $$J_F(X,\rho)=\frac{X}{r-\mu}\cdot\frac{\big(\max\{0,\,1-\rho d/(rX)\}\big)^2}{4\eta}.$$
--
--   This identifies the optimal capacity $I^*(X,\rho)$ and the value function $J_F$ of §2.3 in the scenario without bankruptcy. It is a step of the proof of Proposition 1.
--
--   **Formalization Note** At $\rho=0$ every $I\ge\frac1{2\eta}$ is optimal (the firm produces $Q=\frac1{2\eta}$ and pays nothing for idle capacity), so uniqueness is stated for $\rho>0$.
--
--   Differences from the source:
--   - reading: "the solution to the optimization problem" arg sup_{I≥0} J̃F(X, ρ(X), I), denoted I∗(X, ρ(X)) → max{0, (1/(2η))(1 − ρδ(r − µ)/(rX))} is a maximizer for every ρ ≥ 0 and the only one for ρ > 0; the value J_F holds for every ρ ≥ 0; reason: at ρ = 0, J̃_F(X, 0, ·) is constant on [1/(2η), ∞), so the maximizer is unique only for ρ > 0; every coupon of the equilibrium is > 0
--   - encoding: no bankruptcy option (§3.1): the firm pays coupons perpetually → bankruptcy time τ_B = ∞: integrals over (0, ∞), no bankruptcy term, no α; reason: this is the scenario of Proposition 1
--   - encoding: dx(t) = µx(t)dt + σx(t)dω(t), x(0) = X (p.4) → x(t) = X·exp((µ − σ²/2)t + σW_t) for a Mathlib Brownian motion W (IsBrownianReal), on any probability space; reason: the unique strong solution of the SDE; the statement holds for every probability space carrying a Brownian motion
--   - encoding: σ and r not restricted beyond r > µ, δ called "the unit investment cost" (p.4) → hypotheses σ > 0, r > 0 and δ > 0 (in Params.Standing); reason: r > 0 makes ∫₀^∞ e^{−rt}dt finite and σ ≠ 0 makes the quadratic defining β₁ have two roots; σ > 0 is the volatility convention; δ > 0 is the positivity of a cost and (6) divides by δ(r − µ); only undefined or degenerate cases are excluded
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3 p.5 (I∗(X, ρ(X)) and J_F). Proof step of Proposition 1

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM
import Definitions.Def_DebtDoubleMarg_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **The firm's optimal capacity for a fixed coupon.** Under the standing assumptions, for a
standard Brownian motion `W`, `X > 0` and `ρ ≥ 0`, with `d = δ(r − µ)`:
1. `I₀ = max{0, (1/(2η))(1 − ρd/(rX))}` maximizes `J̃_F(X, ρ, ·)` over `I ≥ 0`;
2. if `ρ > 0` it is the only maximizer;
3. `J_F(X, ρ) = X/(r − µ) · (max{0, 1 − ρd/(rX)})² / (4η)`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3, p.5 (`I*(X, ρ)` and
`J_F(X, ρ)`). A proof step of Proposition 1.

**Formalization Note** At `ρ = 0` every `I ≥ 1/(2η)` is optimal (the firm then produces
`Q = 1/(2η)`), so uniqueness is stated for `ρ > 0` only; the value formula holds for `ρ ≥ 0`. -/
theorem firm_optimal_size (p : Params) (hp : p.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (X ρ : ℝ) (hX : 0 < X) (hρ : 0 ≤ ρ) :
    IsOptimalSize p P W X ρ
        (max 0 (1 / (2 * p.η) * (1 - ρ * (p.δ * (p.r - p.μ)) / (p.r * X)))) ∧
      (0 < ρ → ∀ I : ℝ, IsOptimalSize p P W X ρ I →
        I = max 0 (1 / (2 * p.η) * (1 - ρ * (p.δ * (p.r - p.μ)) / (p.r * X)))) ∧
      firmValue p P W X ρ =
        X / (p.r - p.μ) * (max 0 (1 - ρ * (p.δ * (p.r - p.μ)) / (p.r * X))) ^ 2 / (4 * p.η) := by sorry

end DebtDoubleMarg
