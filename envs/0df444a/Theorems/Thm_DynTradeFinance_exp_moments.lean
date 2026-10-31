-- Prove2me | Theorems.Thm_DynTradeFinance_exp_moments
-- name    : DynTradeFinance.exp_moments
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:11.926542+00:00
-- url     : https://prove2.me/theorems/7c2f8322-a6b8-4864-bc57-a1a498c146f5
-- title:
--   Proof of Proposition 1, p. 38 — $\mathbb E[e^{s\tilde T_1}]=\frac1{1-s}$ and $\mathbb E[ce^{s(\tilde T_1+\tilde T_2)}]=\frac{c}{1-s}\cdot\frac{\mu}{\mu-s}$ (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   Let the model parameters satisfy the standing assumptions, and let $\tilde T_1\sim\mathrm{Exp}(1)$, $\tilde T_2\sim\mathrm{Exp}(\mu)$, $\tilde d\sim\mathrm{Exp}(\lambda)$ be independent. Then
--
--   1. for every $s<1$, $e^{s\tilde T_1}$ is integrable and
--   $$\mathbb E\big[e^{s\tilde T_1}\big]=\frac{1}{1-s};$$
--   2. for every $s<\min(1,\mu)$, $c\,e^{s(\tilde T_1+\tilde T_2)}$ is integrable and
--   $$\mathbb E\big[c\,e^{s(\tilde T_1+\tilde T_2)}\big]=\frac{c}{1-s}\cdot\frac{\mu}{\mu-s}.$$
--
--   The paper uses these at $s=\delta$ (capital cost) and $s=r^*$ (repayment) to turn the pricing equation (45) into (48).
--
--   Differences from the source:
--   - generalization: E[e^{δT̃₁}] = 1/(1−δ) and E[ce^{r*(T̃₁+T̃₂)}] = c/(1−r*)·µ/(µ−r*), at s = δ and s = r* → every s < 1, resp. every s < min(1, µ), with integrability; reason: the domain of convergence contains δ and r*; the statement specializes there
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: the seller 'needs to borrow c from the bank' (p. 7); no sign of c is stated → 0 < c; reason: c is the loan principal; at c ≤ 0 there is no loan and (6) degenerates (4cp₁p₂ ≤ 0)
--   - reading: p₁, p₂ are probabilities, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1 and 0 < p₂ < 1; reason: at p₁p₂ = 0 the expected repayment does not depend on the rate and is below c, so (2) has no solution; the proof divides by p₁ in (50)
--   - generalization: π₀ < Π₀ and 'w sufficiently high' (p. 9) → not assumed; reason: neither enters any formula of §4; the statement without them specializes to the source's setting
--   - encoding: T̃₁ ∼ Exp(1), T̃₂ ∼ Exp(µ), d̃ ∼ Exp(λ), independent (pp. 8–9) → random variables on an arbitrary probability space (Ω, P) with HasLaw … (expMeasure ·) and joint independence iIndepFun of the triple (Clocks); reason: the same instances; the statement holds for every such clocks
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), proof of Proposition 1, p. 38

import Mathlib
import Definitions.Def_DynTradeFinance_Params
import Definitions.Def_DynTradeFinance_Clocks

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **Exponential moments of the clocks** (proof of Proposition 1), Lee, Tang, Yang, Zhang,
*Dynamic trade finance in the presence of information frictions and FinTech*, SSRN 3632563,
p. 38: "Because T̃₁ ∼ Exp(1) and T̃₂ ∼ Exp(µ), we have: E[e^{δT̃₁}] = 1/(1−δ) and
E[ce^{r*(T̃₁+T̃₂)}] = c/(1−r*) · µ/(µ−r*)."

For the model's clocks (`Clocks`: `T₁ ∼ Exp(1)`, `T₂ ∼ Exp(μ)`, `d ∼ Exp(λ)`, independent):
1. for every `s < 1`, `e^{sT₁}` is integrable and `E[e^{sT₁}] = 1/(1 − s)`;
2. for every `s < min(1, μ)`, `c·e^{s(T₁+T₂)}` is integrable and
   `E[c e^{s(T₁+T₂)}] = c/(1 − s) · μ/(μ − s)`.

**Formalization Note.** The page states the identities at `s = δ` and `s = r*`; they are stated
here on the whole domain of convergence, which contains both points. -/
theorem exp_moments (θ : Params) (hθ : θ.Admissible) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T₁ T₂ d : Ω → ℝ) (hcl : Clocks θ P T₁ T₂ d) :
    (∀ s : ℝ, s < 1 →
      Integrable (fun ω => Real.exp (s * T₁ ω)) P ∧
        ∫ ω, Real.exp (s * T₁ ω) ∂P = 1 / (1 - s)) ∧
    (∀ s : ℝ, s < min 1 θ.μ →
      Integrable (fun ω => θ.c * Real.exp (s * (T₁ ω + T₂ ω))) P ∧
        ∫ ω, θ.c * Real.exp (s * (T₁ ω + T₂ ω)) ∂P = θ.c / (1 - s) * (θ.μ / (θ.μ - s))) := by sorry

end DynTradeFinance
