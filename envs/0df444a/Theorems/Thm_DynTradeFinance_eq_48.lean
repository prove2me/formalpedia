-- Prove2me | Theorems.Thm_DynTradeFinance_eq_48
-- name    : DynTradeFinance.eq_48
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:19.166413+00:00
-- url     : https://prove2.me/theorems/8fc9fa74-e948-4d2e-93db-a2cd7b0880b7
-- title:
--   Eq. (48), p. 38 — the UF pricing equation (2) in closed form (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   Let the model parameters satisfy the standing assumptions and let $\tilde T_1,\tilde T_2,\tilde d$ be the model's clocks. For every rate $r<\min(1,\mu)$ (where the expected repayment is finite), $r$ is a competitive UF rate, i.e. satisfies the pricing equation (2) $\mathrm{EP}_U(r)=c+\mathrm{NCC}_U$, if and only if
--   $$(1-p_1)l_1+p_1(1-p_2)l_2+p_1p_2\,\frac{c\mu}{(1-r)(\mu-r)}=c+(c-l_1)\Big(\frac{\delta}{1-\delta}\Big)\Big(1+\frac{p_1}{\mu-\delta}\Big).\qquad(48)$$
--
--   This reduces the UF pricing problem to a quadratic equation in $r$, whose smaller root is the rate $r^*$ of Proposition 1.
--
--   Differences from the source:
--   - generalization: (48), the equation the equilibrium rate r* solves, obtained from (45) → for every r < min(1, µ): r satisfies (2) under UF ↔ (48) holds at r; reason: the derivation (45) → (48) is valid at each r in the finite domain; it specializes at r*
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: the seller 'needs to borrow c from the bank' (p. 7); no sign of c is stated → 0 < c; reason: c is the loan principal; at c ≤ 0 there is no loan and (6) degenerates (4cp₁p₂ ≤ 0)
--   - reading: p₁, p₂ are probabilities, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1 and 0 < p₂ < 1; reason: at p₁p₂ = 0 the expected repayment does not depend on the rate and is below c, so (2) has no solution; the proof divides by p₁ in (50)
--   - generalization: π₀ < Π₀ and 'w sufficiently high' (p. 9) → not assumed; reason: neither enters any formula of §4; the statement without them specializes to the source's setting
--   - encoding: T̃₁ ∼ Exp(1), T̃₂ ∼ Exp(µ), d̃ ∼ Exp(λ), independent (pp. 8–9) → random variables on an arbitrary probability space (Ω, P) with HasLaw … (expMeasure ·) and joint independence iIndepFun of the triple (Clocks); reason: the same instances; the statement holds for every such clocks
--   - encoding: passing Step 1 and Step 2 with probabilities p₁ and p₂, independent of the durations (p. 8) → p₁, p₂ enter as the weights of the paper's mixtures (3)–(5), (8), (58); no Bernoulli variables; reason: the paper's own formulas; the same values
--   - encoding: competitive loan pricing (2): expected repayment = c + NCC → IsCompetitiveUF / IsCompetitiveDTF: the repayment is integrable and EP = c + NCC; reason: the source's equation between real numbers presupposes a finite expected repayment; Lean's Bochner integral of a non-integrable function is 0
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), proof of Proposition 1, Eq. (48), p. 38

import Mathlib
import Definitions.Def_DynTradeFinance_Params
import Definitions.Def_DynTradeFinance_Clocks
import Definitions.Def_DynTradeFinance_UniformFinancing

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **The UF break-even condition in closed form, Eq. (48)** (proof of Proposition 1), Lee, Tang,
Yang, Zhang, SSRN 3632563, p. 38:
`(1 − p₁)l₁ + p₁(1 − p₂)l₂ + p₁p₂·cμ/((1 − r)(μ − r)) = c + (c − l₁)(δ/(1 − δ))(1 + p₁/(μ − δ))`.

For admissible parameters and the model's clocks, and every rate `r < min(1, μ)` (where the
expected repayment is finite), `r` satisfies the competitive loan pricing equation (2) under
uniform financing if and only if (48) holds. -/
theorem eq_48 (θ : Params) (hθ : θ.Admissible) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T₁ T₂ d : Ω → ℝ) (hcl : Clocks θ P T₁ T₂ d)
    (r : ℝ) (hr : r < min 1 θ.μ) :
    IsCompetitiveUF θ P T₁ T₂ r ↔
      (1 - θ.p₁) * θ.l₁ + θ.p₁ * (1 - θ.p₂) * θ.l₂ +
          θ.p₁ * θ.p₂ * (θ.c * θ.μ / ((1 - r) * (θ.μ - r))) =
        θ.c + (θ.c - θ.l₁) * (θ.δ / (1 - θ.δ)) * (1 + θ.p₁ / (θ.μ - θ.δ)) := by sorry

end DynTradeFinance
