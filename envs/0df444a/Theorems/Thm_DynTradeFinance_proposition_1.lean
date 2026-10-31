-- Prove2me | Theorems.Thm_DynTradeFinance_proposition_1
-- name    : DynTradeFinance.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:57.799566+00:00
-- url     : https://prove2.me/theorems/53685ed9-1ce3-446a-9003-a8cfbb4a665d
-- title:
--   Proposition 1, p. 12 — the competitive UF rate is $r^*$ of (6) and $\Pi_U=\Pi_0-(c-l_1)\frac{\delta}{1-\delta}\big(1+\frac{p_1}{\mu-\delta}\big)$ (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   Let the model parameters satisfy the standing assumptions and let $\tilde T_1,\tilde T_2,\tilde d$ be the model's clocks. Let
--   $$r^*=\tfrac12\Big(1+\mu-\sqrt{1+\mu^2-\mu\Big(2-\frac{4cp_1p_2}{c-(1-p_1)l_1-p_1(1-p_2)l_2+\frac{(\mu+p_1-\delta)(c-l_1)\delta}{(1-\delta)(\mu-\delta)}}\Big)}\Big).\qquad(6)$$
--   Then
--
--   1. $r^*<\min(1,\mu)$, so the expected repayment at $r^*$ is finite;
--   2. $r^*$ satisfies the competitive loan pricing equation (2) under uniform financing;
--   3. every rate satisfying (2) under uniform financing equals $r^*$ (the equilibrium rate is unique);
--   4. the seller's payoff at $r^*$ is
--   $$\Pi_U=\Pi_0-(c-l_1)\Big(\frac{\delta}{1-\delta}\Big)\Big(1+\frac{p_1}{\mu-\delta}\Big),\qquad(7)$$
--   where $\Pi_0=p_1p_2w+(1-p_1)l_1+p_1(1-p_2)l_2-c$ is the frictionless value (1).
--
--   The gap $\Pi_0-\Pi_U$ is the inefficiency caused by the regulatory capital requirement under uniform financing; it is the benchmark against which the value of dynamic trade finance is measured.
--
--   Differences from the source:
--   - reading: 'the equilibrium interest rate is r*', the proof choosing 'the smaller one (due to market competition)' of the two roots of (48) (p. 38) → r* < min(1, µ), r* satisfies (2), and every rate satisfying (2) equals r*; reason: the larger root of (48) exceeds max(1, µ), where the expected repayment is infinite and (2) cannot hold
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: the seller 'needs to borrow c from the bank' (p. 7); no sign of c is stated → 0 < c; reason: c is the loan principal; at c ≤ 0 there is no loan and (6) degenerates (4cp₁p₂ ≤ 0)
--   - reading: p₁, p₂ are probabilities, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1 and 0 < p₂ < 1; reason: at p₁p₂ = 0 the expected repayment does not depend on the rate and is below c, so (2) has no solution; the proof divides by p₁ in (50)
--   - generalization: π₀ < Π₀ and 'w sufficiently high' (p. 9) → not assumed; reason: neither enters any formula of §4; the statement without them specializes to the source's setting
--   - encoding: T̃₁ ∼ Exp(1), T̃₂ ∼ Exp(µ), d̃ ∼ Exp(λ), independent (pp. 8–9) → random variables on an arbitrary probability space (Ω, P) with HasLaw … (expMeasure ·) and joint independence iIndepFun of the triple (Clocks); reason: the same instances; the statement holds for every such clocks
--   - encoding: passing Step 1 and Step 2 with probabilities p₁ and p₂, independent of the durations (p. 8) → p₁, p₂ enter as the weights of the paper's mixtures (3)–(5), (8), (58); no Bernoulli variables; reason: the paper's own formulas; the same values
--   - encoding: competitive loan pricing (2): expected repayment = c + NCC → IsCompetitiveUF / IsCompetitiveDTF: the repayment is integrable and EP = c + NCC; reason: the source's equation between real numbers presupposes a finite expected repayment; Lean's Bochner integral of a non-integrable function is 0
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), Proposition 1, Eqs. (6)–(7), p. 12 (proof p. 38)

import Mathlib
import Definitions.Def_DynTradeFinance_Params
import Definitions.Def_DynTradeFinance_Clocks
import Definitions.Def_DynTradeFinance_UniformFinancing

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **Proposition 1** (Uniform Financing), Lee, Tang, Yang, Zhang, SSRN 3632563, p. 12:
"Under Uniform Financing, the equilibrium interest rate is: r* = ½(1 + µ − √(1 + µ² − µ(2 −
4cp₁p₂/(c − (1 − p₁)l₁ − p₁(1 − p₂)l₂ + (µ+p₁−δ)(c−l₁)δ/((1−δ)(µ−δ)))))) (6). The seller's
corresponding payoff is: Π_U = Π₀ − (c − l₁)(δ/(1 − δ))(1 + p₁/(µ − δ)) (7)."

For admissible parameters (with `δ < min(μ,1)`) and the model's clocks:
1. `r*` of (6) lies in the domain `r* < min(1, μ)` where the expected repayment is finite;
2. `r*` satisfies the competitive loan pricing equation (2) under UF;
3. it is the only rate that does (the equilibrium rate);
4. the seller's payoff (3) at `r*` is (7).

**Formalization Note.** Uniqueness reads "the equilibrium interest rate is r*": the proof
(p. 38) takes the smaller of the two roots of (48), the other one lying where the expected
repayment is infinite, which `IsCompetitiveUF` excludes by its integrability requirement. -/
theorem proposition_1 (θ : Params) (hθ : θ.Admissible) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T₁ T₂ d : Ω → ℝ) (hcl : Clocks θ P T₁ T₂ d) :
    rStarUF θ < min 1 θ.μ ∧
    IsCompetitiveUF θ P T₁ T₂ (rStarUF θ) ∧
    (∀ r : ℝ, IsCompetitiveUF θ P T₁ T₂ r → r = rStarUF θ) ∧
    payoffU θ P T₁ T₂ (rStarUF θ) =
      θ.Pi0 - (θ.c - θ.l₁) * (θ.δ / (1 - θ.δ)) * (1 + θ.p₁ / (θ.μ - θ.δ)) := by sorry

end DynTradeFinance
