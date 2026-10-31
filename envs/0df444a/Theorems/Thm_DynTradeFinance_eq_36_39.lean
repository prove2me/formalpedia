-- Prove2me | Theorems.Thm_DynTradeFinance_eq_36_39
-- name    : DynTradeFinance.eq_36_39
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:04.892754+00:00
-- url     : https://prove2.me/theorems/140d79d8-aa77-4567-9340-a9570c6b6b7e
-- title:
--   Appendix C, Eqs. (36)–(39), p. 34 — $\Pr(\tilde d<\tilde T_2)$ and the conditional exponential moments given $\tilde d<\tilde T_2$, $\tilde d\ge\tilde T_2$ (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   Let the model parameters satisfy the standing assumptions. Let $\tilde X_1\sim\mathrm{Exp}(1)$, $\tilde T_2\sim\mathrm{Exp}(\mu)$ and $\tilde d\sim\mathrm{Exp}(\lambda)$ be independent, let $K_1\ge0$ be a constant, and let the Step-1 completion time be $\tilde T_1=K_1+\tilde X_1$. Then
--
--   1. $\displaystyle\Pr(\tilde d<\tilde T_2)=1-\frac{\mu}{\lambda+\mu}$; (36)
--   2. $\displaystyle\mathbb E\big[e^{\delta(\tilde T_1+\tilde T_2)}\,\big|\,\tilde d<\tilde T_2\big]=\frac{e^{\delta K_1}\mu(\lambda+\mu)}{(1-\delta)(\mu-\delta)(\lambda+\mu-\delta)}$; (37)
--   3. $\displaystyle\mathbb E\big[e^{\delta(\tilde T_1+\tilde d)}\,\big|\,\tilde d<\tilde T_2\big]=\frac{e^{\delta K_1}(\lambda+\mu)}{(1-\delta)(\mu+\lambda-\delta)}$; (38)
--   4. $\displaystyle\mathbb E\big[e^{\delta(\tilde T_1+\tilde T_2)}\,\big|\,\tilde d\ge\tilde T_2\big]=\frac{e^{\delta K_1}(\lambda+\mu)}{(1-\delta)(\lambda+\mu-\delta)}$. (39)
--
--   The main model is the case $K_1=0$; these are the expectations that make the DTF net cost of capital explicit.
--
--   Differences from the source:
--   - encoding: E[X | A] and Pr(A) for A = {d̃ < T̃₂}, {d̃ ≥ T̃₂} → the integral against Mathlib's conditional measure P[|A] = P(A)⁻¹ • P restricted to A, and P.real A; reason: the definition of conditional expectation given an event of positive probability
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: the seller 'needs to borrow c from the bank' (p. 7); no sign of c is stated → 0 < c; reason: c is the loan principal; at c ≤ 0 there is no loan and (6) degenerates (4cp₁p₂ ≤ 0)
--   - reading: p₁, p₂ are probabilities, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1 and 0 < p₂ < 1; reason: at p₁p₂ = 0 the expected repayment does not depend on the rate and is below c, so (2) has no solution; the proof divides by p₁ in (50)
--   - generalization: π₀ < Π₀ and 'w sufficiently high' (p. 9) → not assumed; reason: neither enters any formula of §4; the statement without them specializes to the source's setting
--   - encoding: X̃₁ ∼ Exp(1), T̃₂ ∼ Exp(µ) independent (p. 34), d̃ ∼ Exp(λ) independent of processing time (p. 9) → Clocks θ P X₁ T₂ d: HasLaw … (expMeasure ·) and joint independence iIndepFun of (X̃₁, T̃₂, d̃) on an arbitrary probability space; T̃₁ := K₁ + X̃₁; reason: the same instances; the statement holds for every such random variables
--   - reading: T̃₁ 'consists a constant component K₁' (p. 33), 'the fixed production time' (p. 34); no sign of K₁ is stated → K₁ ≥ 0; reason: K₁ is a duration
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), Appendix C, Eqs. (36)–(39), p. 34 (K₁ = 0 cases in the proof of Proposition 2, p. 39)

import Mathlib
import Definitions.Def_DynTradeFinance_Params
import Definitions.Def_DynTradeFinance_Clocks

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **Conditional exponential moments, Appendix C, Eqs. (36)–(39)**, Lee, Tang, Yang, Zhang,
SSRN 3632563, p. 34. The Step-1 completion time is `T̃₁ = K₁ + X̃₁` with a constant component
`K₁ ≥ 0` and `X̃₁ ∼ Exp(1)`; `T̃₂ ∼ Exp(μ)` and `d̃ ∼ Exp(λ)`, all independent. Then
* (36) `Pr(d̃ < T̃₂) = 1 − μ/(λ + μ)`;
* (37) `E[e^{δ(T̃₁+T̃₂)} | d̃ < T̃₂] = e^{δK₁}μ(λ + μ)/((1 − δ)(μ − δ)(λ + μ − δ))`;
* (38) `E[e^{δ(T̃₁+d̃)} | d̃ < T̃₂] = e^{δK₁}(λ + μ)/((1 − δ)(μ + λ − δ))`;
* (39) `E[e^{δ(T̃₁+T̃₂)} | d̃ ≥ T̃₂] = e^{δK₁}(λ + μ)/((1 − δ)(λ + μ − δ))`.

**Formalization Note.** `Clocks θ P X₁ T₂ d` gives the laws and independence of `X̃₁, T̃₂, d̃`;
the main model is `K₁ = 0`. `E[· | A]` is the integral against Mathlib's conditional measure
`P[|A] = P(A)⁻¹ • P|_A`. -/
theorem eq_36_39 (θ : Params) (hθ : θ.Admissible) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₁ T₂ d : Ω → ℝ) (hcl : Clocks θ P X₁ T₂ d)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁) :
    P.real {ω | d ω < T₂ ω} = 1 - θ.μ / (θ.lam + θ.μ) ∧
    ∫ ω, Real.exp (θ.δ * ((K₁ + X₁ ω) + T₂ ω)) ∂(P[|{ω | d ω < T₂ ω}]) =
      Real.exp (θ.δ * K₁) * θ.μ * (θ.lam + θ.μ) /
        ((1 - θ.δ) * (θ.μ - θ.δ) * (θ.lam + θ.μ - θ.δ)) ∧
    ∫ ω, Real.exp (θ.δ * ((K₁ + X₁ ω) + d ω)) ∂(P[|{ω | d ω < T₂ ω}]) =
      Real.exp (θ.δ * K₁) * (θ.lam + θ.μ) / ((1 - θ.δ) * (θ.μ + θ.lam - θ.δ)) ∧
    ∫ ω, Real.exp (θ.δ * ((K₁ + X₁ ω) + T₂ ω)) ∂(P[|{ω | T₂ ω ≤ d ω}]) =
      Real.exp (θ.δ * K₁) * (θ.lam + θ.μ) / ((1 - θ.δ) * (θ.lam + θ.μ - θ.δ)) := by sorry

end DynTradeFinance
