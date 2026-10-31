-- Prove2me | Theorems.Thm_DynTradeFinance_proposition_2
-- name    : DynTradeFinance.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:03.679691+00:00
-- url     : https://prove2.me/theorems/b9a5f418-34d3-4f62-abe5-4e0c586e7288
-- title:
--   Proposition 2, p. 14 — below the threshold $\bar r_2^*$ every $r_2$ has a competitive $r_1\ge r_2$, and $\Pi_D$ is (9) (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   Let the model parameters satisfy the standing assumptions and let $\tilde T_1,\tilde T_2,\tilde d$ be the model's clocks. Let $\bar r_2^*=\min(r_2^{C,0},\bar r_2)$ with $r_2^{C,0}$ and $\bar r_2$ given by (30) and (31). Then
--
--   1. for every $r_2\le\bar r_2^*$ there is a rate $r_1<\min(1,\lambda+\mu)$ with $r_1\ge r_2$ such that $(r_1,r_2)$ satisfies the bank's competitive loan pricing equation (2) under DTF — so the bank can offer any such schedule;
--   2. for every schedule $(r_1,r_2)$ satisfying (2) under DTF, the seller's payoff (8) is
--   $$\Pi_D=\Pi_0-\frac{\delta}{1-\delta}\Big[(c-l_1)\Big(1+\frac{p_1}{\lambda+\mu-\delta}\Big)+\frac{(c-l_2)\lambda p_1}{(\lambda+\mu-\delta)(\mu-\delta)}\Big].\qquad(9)$$
--
--   The competitive DTF schedules are not unique, but the seller's payoff is the same for all of them; comparing (9) with (7) gives the value of DTF.
--
--   Differences from the source:
--   - reading: 'there exists a threshold r̄₂* such that the bank could offer any interest rate schedule (r₁*, r₂*) where r₂* ≤ r̄₂* and (r₁*, r₂*) satisfy … (2)' → the explicit r̄₂* = min(r₂^{C,0}, r̄₂) of (30)–(31); for every r₂ ≤ r̄₂* there is r₁ < min(1, λ + µ) with r₁ ≥ r₂ such that (r₁, r₂) satisfies (2); reason: the proof (p. 39) defines r̄₂* this way; Proposition B.1 enters only through (30)–(31); r₁ ≥ r₂ is B.1's constraint 'refinancing only results in interest rate reduction' (p. 40); B.1's second constraint (no cheaper competitive refinancing, through Proposition E.1) is a claim of B.1, not of Proposition 2, and is not stated here; the contract's strict r₁ > r₂ (p. 10) cannot hold at r₂ = r̄₂, where (64) gives r₁ = r̄₂, so the weak form of B.1 is used
--   - generalization: the payoff (9) 'under such an interest rate schedule' (r₂* ≤ r̄₂*) → (9) for every schedule satisfying (2) under DTF; reason: the statement specializes to the schedules with r₂ ≤ r̄₂*
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: the seller 'needs to borrow c from the bank' (p. 7); no sign of c is stated → 0 < c; reason: c is the loan principal; at c ≤ 0 there is no loan and (6) degenerates (4cp₁p₂ ≤ 0)
--   - reading: p₁, p₂ are probabilities, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1 and 0 < p₂ < 1; reason: at p₁p₂ = 0 the expected repayment does not depend on the rate and is below c, so (2) has no solution; the proof divides by p₁ in (50)
--   - generalization: π₀ < Π₀ and 'w sufficiently high' (p. 9) → not assumed; reason: neither enters any formula of §4; the statement without them specializes to the source's setting
--   - encoding: T̃₁ ∼ Exp(1), T̃₂ ∼ Exp(µ), d̃ ∼ Exp(λ), independent (pp. 8–9) → random variables on an arbitrary probability space (Ω, P) with HasLaw … (expMeasure ·) and joint independence iIndepFun of the triple (Clocks); reason: the same instances; the statement holds for every such clocks
--   - encoding: passing Step 1 and Step 2 with probabilities p₁ and p₂, independent of the durations (p. 8) → p₁, p₂ enter as the weights of the paper's mixtures (3)–(5), (8), (58); no Bernoulli variables; reason: the paper's own formulas; the same values
--   - encoding: competitive loan pricing (2): expected repayment = c + NCC → IsCompetitiveUF / IsCompetitiveDTF: the repayment is integrable and EP = c + NCC; reason: the source's equation between real numbers presupposes a finite expected repayment; Lean's Bochner integral of a non-integrable function is 0
--   - encoding: the terms Pr(A)·E[X | A] of (8) and (58) → E[X·1_A], as one expectation of the pathwise repayment (dtfRepayPath) or capital cost; reason: the same values; avoids dividing by Pr(A)
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), Proposition 2, Eq. (9), p. 14 (proof p. 39; threshold from Proposition B.1, Eqs. (30)–(31), p. 33, and (63)–(66), p. 40)

import Mathlib
import Definitions.Def_DynTradeFinance_Params
import Definitions.Def_DynTradeFinance_Clocks
import Definitions.Def_DynTradeFinance_DynamicFinancing

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **Proposition 2** (DTF), Lee, Tang, Yang, Zhang, SSRN 3632563, p. 14: "Under the DTF
contract, there exists a threshold r̄₂* such that the bank could offer any interest rate schedule
(r₁*, r₂*) where r₂* ≤ r̄₂* and (r₁*, r₂*) satisfy the bank's competitive loan pricing
equation (2). The seller's payoff under such an interest rate schedule is:
Π_D = Π₀ − δ/(1 − δ)[(c − l₁)(1 + p₁/(λ + µ − δ)) + (c − l₂)λp₁/((λ + µ − δ)(µ − δ))]. (9)"

With the threshold `r̄₂* = min(r₂^{C,0}, r̄₂)` of the proof (p. 39) and Proposition B.1 ((30),
(31), p. 33), for admissible parameters and the model's clocks:
1. for every `r₂ ≤ r̄₂*` there is `r₁ < min(1, λ + μ)` with `r₁ ≥ r₂` such that `(r₁, r₂)`
   satisfies the competitive loan pricing equation (2) under DTF;
2. every schedule `(r₁, r₂)` satisfying (2) under DTF gives the seller the payoff (9).

**Formalization Note.** Item 1 reads "the bank could offer any interest rate schedule … where
r₂* ≤ r̄₂*": the competitive `r₁` exists, lies where the expected repayment is finite, and does
not fall below `r₂` ("refinancing only results in interest rate reduction", p. 40). Item 2 holds
for every competitive schedule, not only those with `r₂ ≤ r̄₂*`. -/
theorem proposition_2 (θ : Params) (hθ : θ.Admissible) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T₁ T₂ d : Ω → ℝ) (hcl : Clocks θ P T₁ T₂ d) :
    (∀ r₂ : ℝ, r₂ ≤ r2barStar θ →
      ∃ r₁ : ℝ, r₁ < min 1 (θ.lam + θ.μ) ∧ r₂ ≤ r₁ ∧ IsCompetitiveDTF θ P T₁ T₂ d r₁ r₂) ∧
    (∀ r₁ r₂ : ℝ, IsCompetitiveDTF θ P T₁ T₂ d r₁ r₂ →
      payoffD θ P T₁ T₂ d r₁ r₂ =
        θ.Pi0 - θ.δ / (1 - θ.δ) * ((θ.c - θ.l₁) * (1 + θ.p₁ / (θ.lam + θ.μ - θ.δ)) +
          (θ.c - θ.l₂) * θ.lam * θ.p₁ / ((θ.lam + θ.μ - θ.δ) * (θ.μ - θ.δ)))) := by sorry

end DynTradeFinance
