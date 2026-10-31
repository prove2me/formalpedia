-- Prove2me | Theorems.Thm_DebtDoubleMarg_firmNPV_eq
-- name    : DebtDoubleMarg.firmNPV_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:51.105912+00:00
-- url     : https://prove2.me/theorems/243e6f69-4217-4e45-b7f4-a34506347cc6
-- title:
--   (8) without bankruptcy — the firm's NPV $\tilde J_F(X,\rho,I)=\frac{X}{r-\mu}R(I)-\frac{\rho}{r}\delta I$
-- statement:
--   Assume the standing assumptions ($\eta>0$, $r>\mu$, $\delta>0$, $\sigma>0$, $r>0$) and let the demand be driven by a standard Brownian motion. For an investment level $X>0$, a coupon rate $\rho\ge0$ and a capacity $I\ge0$, the firm's net present value without bankruptcy satisfies
--   $$\tilde J_F(X,\rho,I)=\mathbb E\Big[\int_0^\infty e^{-rt}\pi\big(x^X(t),I;\rho\big)dt\Big]=\frac{X}{r-\mu}R(I)-\frac{\rho}{r}\delta I,\qquad R(I)=\sup_{0\le Q\le I}(1-\eta Q)Q.$$
--   In particular, if $I\le\frac1{2\eta}$,
--   $$\tilde J_F(X,\rho,I)=\frac{X}{r-\mu}I(1-\eta I)-\frac{\rho}{r}\delta I.$$
--
--   This is (8) of the paper with $\tau_B=\infty$: the first two terms, cash inflows and coupon payments, remain, and the third term, which "corrects for the fact that these cash flows only take place until the firm is bankrupt", is absent. It is a step of the proof of Proposition 1.
--
--   Differences from the source:
--   - encoding: no bankruptcy option (§3.1): the firm pays coupons perpetually → bankruptcy time τ_B = ∞: integrals over (0, ∞), no bankruptcy term, no α; reason: this is the scenario of Proposition 1
--   - encoding: (8)'s first term X I(1 − ηI)/(r − µ), after replacing Q(t) by I (p.5) → X·sup_{0≤Q≤I}(1 − ηQ)Q/(r − µ) for every I ≥ 0, and the printed form when I ≤ 1/(2η); reason: π keeps the supremum over Q of p.5; the replacement Q = I is exact precisely for I ≤ 1/(2η)
--   - encoding: dx(t) = µx(t)dt + σx(t)dω(t), x(0) = X (p.4) → x(t) = X·exp((µ − σ²/2)t + σW_t) for a Mathlib Brownian motion W (IsBrownianReal), on any probability space; reason: the unique strong solution of the SDE; the statement holds for every probability space carrying a Brownian motion
--   - encoding: σ and r not restricted beyond r > µ, δ called "the unit investment cost" (p.4) → hypotheses σ > 0, r > 0 and δ > 0 (in Params.Standing); reason: r > 0 makes ∫₀^∞ e^{−rt}dt finite and σ ≠ 0 makes the quadratic defining β₁ have two roots; σ > 0 is the volatility convention; δ > 0 is the positivity of a cost and (6) divides by δ(r − µ); only undefined or degenerate cases are excluded
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, (8) p.9 (first two terms), and §2.3 p.5 (Q = 1/(2η)). Proof step of Proposition 1

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM
import Definitions.Def_DebtDoubleMarg_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **The firm's NPV without bankruptcy.** Under the standing assumptions, for a standard
Brownian motion `W`, `X > 0`, `ρ ≥ 0` and `I ≥ 0`,
`J̃_F(X, ρ, I) = X · R(I)/(r − µ) − (ρ/r) δ I` with `R(I) = sup_{0≤Q≤I} (1 − ηQ)Q`; in particular
`J̃_F(X, ρ, I) = X/(r − µ) · I(1 − ηI) − (ρ/r) δ I` when `I ≤ 1/(2η)`.

Huberts et al., Management Science (2025), doi:10.1287/mnsc.2023.01152, (8), p.9 (its first two
terms; the third, bankruptcy, term is absent because `τ_B = ∞`), and §2.3, p.5 (`Q = 1/(2η)`
maximizes the revenue part). A proof step of Proposition 1. -/
theorem firmNPV_eq (p : Params) (hp : p.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (X ρ I : ℝ) (hX : 0 < X) (hρ : 0 ≤ ρ) (hI : 0 ≤ I) :
    firmNPV p P W X ρ I =
        X * sSup ((fun Q : ℝ => (1 - p.η * Q) * Q) '' Set.Icc 0 I) / (p.r - p.μ)
          - ρ / p.r * p.δ * I ∧
      (I ≤ 1 / (2 * p.η) →
        firmNPV p P W X ρ I = X / (p.r - p.μ) * I * (1 - p.η * I) - ρ / p.r * p.δ * I) := by sorry

end DebtDoubleMarg
