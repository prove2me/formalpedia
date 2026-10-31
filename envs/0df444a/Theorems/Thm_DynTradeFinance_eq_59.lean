-- Prove2me | Theorems.Thm_DynTradeFinance_eq_59
-- name    : DynTradeFinance.eq_59
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:04.101633+00:00
-- url     : https://prove2.me/theorems/87ff6a3c-1897-4061-8f5c-4537d12b20b6
-- title:
--   Eq. (59), p. 39 — the DTF pricing equation (2) in closed form (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   Let the model parameters satisfy the standing assumptions and let $\tilde T_1,\tilde T_2,\tilde d$ be the model's clocks. For every schedule with $r_1<\min(1,\lambda+\mu)$ and $r_2<\mu$ (where the expected DTF repayment is finite), $(r_1,r_2)$ is a competitive DTF schedule, i.e. satisfies the pricing equation (2) in the form (58), if and only if
--   $$\frac{c\mu p_1p_2(\lambda+\mu-r_2)}{(\lambda+\mu-r_1)(1-r_1)(\mu-r_2)}=c-(1-p_1)l_1-p_1(1-p_2)l_2+\frac{\delta}{1-\delta}\Big[(c-l_1)\Big(1+\frac{p_1}{\lambda+\mu-\delta}\Big)+\frac{(c-l_2)\lambda p_1}{(\lambda+\mu-\delta)(\mu-\delta)}\Big].\qquad(59)$$
--
--   This is the single equation linking the two rates of a competitive DTF schedule; the bracket on the right is the DTF net cost of capital.
--
--   Differences from the source:
--   - generalization: (59), the equation a competitive schedule (r₁*, r₂*) satisfies, obtained from (58) → for every r₁ < min(1, λ + µ) and r₂ < µ: (r₁, r₂) satisfies (2) under DTF ↔ (59) holds; reason: the derivation (58) → (59) is valid at each schedule in the finite domain; it specializes at (r₁*, r₂*)
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: the seller 'needs to borrow c from the bank' (p. 7); no sign of c is stated → 0 < c; reason: c is the loan principal; at c ≤ 0 there is no loan and (6) degenerates (4cp₁p₂ ≤ 0)
--   - reading: p₁, p₂ are probabilities, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1 and 0 < p₂ < 1; reason: at p₁p₂ = 0 the expected repayment does not depend on the rate and is below c, so (2) has no solution; the proof divides by p₁ in (50)
--   - generalization: π₀ < Π₀ and 'w sufficiently high' (p. 9) → not assumed; reason: neither enters any formula of §4; the statement without them specializes to the source's setting
--   - encoding: T̃₁ ∼ Exp(1), T̃₂ ∼ Exp(µ), d̃ ∼ Exp(λ), independent (pp. 8–9) → random variables on an arbitrary probability space (Ω, P) with HasLaw … (expMeasure ·) and joint independence iIndepFun of the triple (Clocks); reason: the same instances; the statement holds for every such clocks
--   - encoding: passing Step 1 and Step 2 with probabilities p₁ and p₂, independent of the durations (p. 8) → p₁, p₂ enter as the weights of the paper's mixtures (3)–(5), (8), (58); no Bernoulli variables; reason: the paper's own formulas; the same values
--   - encoding: competitive loan pricing (2): expected repayment = c + NCC → IsCompetitiveUF / IsCompetitiveDTF: the repayment is integrable and EP = c + NCC; reason: the source's equation between real numbers presupposes a finite expected repayment; Lean's Bochner integral of a non-integrable function is 0
--   - encoding: the terms Pr(A)·E[X | A] of (8) and (58) → E[X·1_A], as one expectation of the pathwise repayment (dtfRepayPath) or capital cost; reason: the same values; avoids dividing by Pr(A)
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), proof of Proposition 2, Eq. (59), p. 39

import Mathlib
import Definitions.Def_DynTradeFinance_Params
import Definitions.Def_DynTradeFinance_Clocks
import Definitions.Def_DynTradeFinance_DynamicFinancing

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **The DTF break-even condition in closed form, Eq. (59)** (proof of Proposition 2), Lee,
Tang, Yang, Zhang, SSRN 3632563, p. 39: "Based on Eq. (58), the interest rate schedule
(r₁*, r₂*) satisfies:
cµp₁p₂(λ + µ − r₂)/((λ + µ − r₁)(1 − r₁)(µ − r₂)) = c − (1 − p₁)l₁ − p₁(1 − p₂)l₂ +
δ/(1 − δ)[(c − l₁)(1 + p₁/(λ + µ − δ)) + (c − l₂)λp₁/((λ + µ − δ)(µ − δ))]."

For admissible parameters, the model's clocks, and every schedule with `r₁ < min(1, λ + μ)`
and `r₂ < μ` (where the expected DTF repayment is finite), `(r₁, r₂)` satisfies the
competitive loan pricing equation (2) under DTF, i.e. (58), if and only if (59) holds. -/
theorem eq_59 (θ : Params) (hθ : θ.Admissible) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T₁ T₂ d : Ω → ℝ) (hcl : Clocks θ P T₁ T₂ d)
    (r₁ r₂ : ℝ) (hr₁ : r₁ < min 1 (θ.lam + θ.μ)) (hr₂ : r₂ < θ.μ) :
    IsCompetitiveDTF θ P T₁ T₂ d r₁ r₂ ↔
      θ.c * θ.μ * θ.p₁ * θ.p₂ * (θ.lam + θ.μ - r₂) /
          ((θ.lam + θ.μ - r₁) * (1 - r₁) * (θ.μ - r₂)) =
        θ.c - (1 - θ.p₁) * θ.l₁ - θ.p₁ * (1 - θ.p₂) * θ.l₂ +
          θ.δ / (1 - θ.δ) * ((θ.c - θ.l₁) * (1 + θ.p₁ / (θ.lam + θ.μ - θ.δ)) +
            (θ.c - θ.l₂) * θ.lam * θ.p₁ / ((θ.lam + θ.μ - θ.δ) * (θ.μ - θ.δ))) := by sorry

end DynTradeFinance
