-- Prove2me | Theorems.Thm_DynTradeFinance_proposition_3
-- name    : DynTradeFinance.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:13.281637+00:00
-- url     : https://prove2.me/theorems/c5477039-9714-40fc-adfb-7396dc9c5829
-- title:
--   Proposition 3, p. 14 — the value of DTF is $V=p_1(l_2-l_1)\frac{\delta}{(1-\delta)(\mu-\delta)}\frac{\lambda}{\lambda+\mu-\delta}$, with its comparative statics (corrected: $\delta<\min(\mu,1)$)
-- statement:
--   Let the model parameters satisfy the standing assumptions $0<p_1,p_2<1$, $l_1<l_2<c<w$, $c>0$, $0<\mu<\lambda$, $0<\delta<\min(\mu,1)$, and let $\tilde T_1\sim\mathrm{Exp}(1)$, $\tilde T_2\sim\mathrm{Exp}(\mu)$, $\tilde d\sim\mathrm{Exp}(\lambda)$ be independent. Write
--   $$F(p_1,l_1,l_2,\mu,\lambda,\delta)=p_1(l_2-l_1)\,\frac{\delta}{(1-\delta)(\mu-\delta)}\cdot\frac{\lambda}{\lambda+\mu-\delta}\qquad(10)$$
--   and, with the expected information delay $\bar d=1/\lambda$, let $\mathrm{MB}=-\partial F/\partial\bar d$ be the marginal benefit of reducing the delay. Then:
--
--   1. **Existence.** A competitive UF rate exists, and a competitive DTF schedule $(r_1,r_2)$ with $r_1>r_2$ exists.
--   2. **Value of DTF.** For every competitive UF rate $r$ and every competitive DTF schedule $(r_1,r_2)$,
--   $$V=\Pi_D(r_1,r_2)-\Pi_U(r)=F(p_1,l_1,l_2,\mu,\lambda,\delta).$$
--   3. **Item 1.** $F$ is strictly increasing in $p_1$ on $(0,1)$; strictly decreasing in $\mu$ on $(\delta,\lambda)$, i.e. increasing in the expected Step-2 time $1/\mu$; strictly increasing in $\delta$ on $(0,\min(\mu,1))$; and it depends on $(l_1,l_2)$ only through $l_2-l_1$ and is strictly increasing in $l_2-l_1>0$.
--   4. **Item 2.** As a function of $\bar d=1/\lambda$, $F$ is strictly decreasing on $(0,1/\mu)$. Moreover, reducing the delay is more beneficial when $\bar d$ is small, $p_1$ is high, $l_2-l_1$ is high, $\mu$ is small and $\delta$ is high: $\mathrm{MB}$ is strictly decreasing in $\bar d$ on $(0,1/\mu)$, and at $\bar d=1/\lambda$ it is strictly increasing in $p_1$ on $(0,1)$, depends on $(l_1,l_2)$ only through $l_2-l_1$ and is strictly increasing in $l_2-l_1>0$, is strictly decreasing in $\mu$ on $(\delta,1/\bar d)$, and strictly increasing in $\delta$ on $(0,\min(\mu,1))$.
--
--   Each monotonicity holds with the other parameters fixed. The value of DTF comes from the bank's ability to hold the smaller capital $c-l_2$ once Step 1 is verified, which is why it scales with $p_1(l_2-l_1)$ and shrinks as verification takes longer.
--
--   **Formalization Note** Competitive rates are those satisfying the bank's pricing equation (2) with a finite expected repayment. The monotonicity clauses are stated for the closed form $F$; clause 2 identifies $F$ with $\Pi_D-\Pi_U$ of the model.
--
--   Differences from the source:
--   - correction: δ ≤ min(µ, 1) (p. 11) → 0 < δ, δ < µ and δ < 1; reason: at equality the expected capital cost is infinite and (7), (9), (10) divide by µ − δ = 0: δ = µ = 1/2, p₁ = p₂ = 1/2, l₁ = 0, l₂ = 1/2, c = 1, w = 2, λ = 1 meets every assumption of §§3–4, yet E[e^{δ(T̃₁+T̃₂)}] = ∞ since T̃₂ ∼ Exp(1/2); footnote 15 states the assumption is there to keep the expected financing cost finite
--   - reading: the seller 'needs to borrow c from the bank' (p. 7); no sign of c is stated → 0 < c; reason: c is the loan principal; at c ≤ 0 there is no loan and (6) degenerates (4cp₁p₂ ≤ 0)
--   - reading: p₁, p₂ are probabilities, with 'p₁, p₂ < 1' in the proof of Proposition 1 (p. 38); no lower bound is stated → 0 < p₁ < 1 and 0 < p₂ < 1; reason: at p₁p₂ = 0 the expected repayment does not depend on the rate and is below c, so (2) has no solution; the proof divides by p₁ in (50)
--   - generalization: π₀ < Π₀ and 'w sufficiently high' (p. 9) → not assumed; reason: neither enters any formula of §4; the statement without them specializes to the source's setting
--   - encoding: T̃₁ ∼ Exp(1), T̃₂ ∼ Exp(µ), d̃ ∼ Exp(λ), independent (pp. 8–9) → random variables on an arbitrary probability space (Ω, P) with HasLaw … (expMeasure ·) and joint independence iIndepFun of the triple (Clocks); reason: the same instances; the statement holds for every such clocks
--   - encoding: passing Step 1 and Step 2 with probabilities p₁ and p₂, independent of the durations (p. 8) → p₁, p₂ enter as the weights of the paper's mixtures (3)–(5), (8), (58); no Bernoulli variables; reason: the paper's own formulas; the same values
--   - encoding: competitive loan pricing (2): expected repayment = c + NCC → IsCompetitiveUF / IsCompetitiveDTF: the repayment is integrable and EP = c + NCC; reason: the source's equation between real numbers presupposes a finite expected repayment; Lean's Bochner integral of a non-integrable function is 0
--   - encoding: the terms Pr(A)·E[X | A] of (8) and (58) → E[X·1_A], as one expectation of the pathwise repayment (dtfRepayPath) or capital cost; reason: the same values; avoids dividing by Pr(A)
--   - reading: V = Π_D − Π_U, 'the difference between the seller's payoffs under DTF and UF' (p. 14), at the competitive rates of Propositions 1–2 → for every competitive UF rate r and every competitive DTF schedule (r₁, r₂), Π_D − Π_U = (10); and a competitive UF rate and a competitive DTF schedule with r₁ > r₂ exist; reason: makes the identity non-vacuous; the paper presupposes both rates (Propositions 1–2, and the contract's r₁ > r₂, p. 10)
--   - generalization: Π_D at the schedules of Proposition 2 (r₂ ≤ r̄₂*) → Π_D at every competitive DTF schedule; reason: the statement specializes to the schedules with r₂ ≤ r̄₂*
--   - reading: 'V increases / decreases in …' → strictly increasing / decreasing on the parameter's whole admissible interval (p₁ ∈ (0,1), µ ∈ (δ, λ), δ ∈ (0, min(µ,1)), d̄ ∈ (0, 1/µ)) with the other parameters fixed; reason: all factors of (10) are positive under the standing assumptions, so the strict reading is the paper's
--   - reading: 'V increases in … the expected processing time of Step 2 (1/µ)' → F strictly decreasing in µ on (δ, λ); reason: 1/µ increases exactly when µ decreases
--   - generalization: 'V increases in … the difference in liquidation value (l₂ − l₁)', with l₁ < l₂ < c → F (and MB) depend on (l₁, l₂) only through l₂ − l₁ and are strictly increasing in it over all positive differences; reason: the constraint l₂ < c does not enter (10); the statement specializes to admissible (l₁, l₂)
--   - reading: 'reducing information delay is more beneficial when d̄ is small, p₁ is high, (l₂ − l₁) is high, µ is small, and δ is high' → the marginal benefit MB = −∂F/∂d̄ (F at λ = 1/d̄) is strictly decreasing in d̄ on (0, 1/µ) and, at d̄ = 1/λ, strictly increasing in p₁ and in l₂ − l₁, strictly decreasing in µ on (δ, 1/d̄), strictly increasing in δ on (0, min(µ,1)); reason: the proof reads item 2 as the signs of ∂²V/∂d² and of the cross derivatives (70)–(75)
--   - encoding: d̄ := 1/λ and ∂V/∂d̄ → F evaluated at λ = 1/d̄; MB is Lean's deriv of that explicit function (marginalBenefit); reason: the function is differentiable at every d̄ > 0, so deriv is the genuine derivative
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), Proposition 3, Eq. (10), p. 14 (proof pp. 40–41)

import Mathlib
import Definitions.Def_DynTradeFinance_Params
import Definitions.Def_DynTradeFinance_Clocks
import Definitions.Def_DynTradeFinance_UniformFinancing
import Definitions.Def_DynTradeFinance_DynamicFinancing
import Definitions.Def_DynTradeFinance_ValueOfDTF

open MeasureTheory ProbabilityTheory

namespace DynTradeFinance

/-- **Proposition 3** (value of DTF), Lee, Tang, Yang, Zhang, *Dynamic trade finance in the
presence of information frictions and FinTech*, SSRN 3632563, p. 14: "In the presence of
regulatory capital requirement, the value of DTF (V) is:
V = p₁(l₂ − l₁) δ/((1 − δ)(µ − δ)) · λ/(λ + µ − δ) (10)
1. V increases in the passing probability of Step 1 (p₁), the expected processing time of Step 2
(1/µ), the bank's cost of capital (δ), and the difference in liquidation value (l₂ − l₁).
2. V decreases in the expected information delay d̄ := 1/λ. Specifically, reducing information
delay is more beneficial when d̄ is small, p₁ is high, (l₂ − l₁) is high, µ is small, and δ is
high." Here V = Π_D − Π_U (p. 14).

For admissible parameters θ (with `δ < min(μ, 1)`) and the model's clocks, writing
`F = valueFormula` for the right side of (10) and `MB = marginalBenefit` for `−∂V/∂d̄`:
* (a) a competitive UF rate exists, and a competitive DTF schedule with `r₁ > r₂` exists;
* (b) for every competitive UF rate `r` and every competitive DTF schedule `(r₁, r₂)`,
  `Π_D(r₁, r₂) − Π_U(r) = F(p₁, l₁, l₂, μ, λ, δ)`;
* (c) item 1: `F` is strictly increasing in `p₁` on `(0, 1)`, strictly decreasing in `μ` on
  `(δ, λ)` (increasing in `1/μ`), strictly increasing in `δ` on `(0, min(μ, 1))`, depends on
  `(l₁, l₂)` only through `l₂ − l₁` and is strictly increasing in it;
* (d) item 2: `d̄ ↦ F(…, λ = 1/d̄, …)` is strictly decreasing on `(0, 1/μ)`; `MB` is strictly
  decreasing in `d̄` on `(0, 1/μ)`, strictly increasing in `p₁` on `(0, 1)`, depends on
  `(l₁, l₂)` only through `l₂ − l₁` and is strictly increasing in it, strictly decreasing in `μ`
  on `(δ, 1/d̄)`, and strictly increasing in `δ` on `(0, min(μ, 1))`, at `d̄ = 1/λ`.
Each monotonicity holds with the other parameters fixed at θ. -/
theorem proposition_3 (θ : Params) (hθ : θ.Admissible) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T₁ T₂ d : Ω → ℝ) (hcl : Clocks θ P T₁ T₂ d) :
    -- (a) existence of competitive rates
    ((∃ r : ℝ, IsCompetitiveUF θ P T₁ T₂ r) ∧
      (∃ r₁ r₂ : ℝ, r₂ < r₁ ∧ IsCompetitiveDTF θ P T₁ T₂ d r₁ r₂)) ∧
    -- (b) the value of DTF, (10)
    (∀ r r₁ r₂ : ℝ, IsCompetitiveUF θ P T₁ T₂ r → IsCompetitiveDTF θ P T₁ T₂ d r₁ r₂ →
      payoffD θ P T₁ T₂ d r₁ r₂ - payoffU θ P T₁ T₂ r =
        valueFormula θ.p₁ θ.l₁ θ.l₂ θ.μ θ.lam θ.δ) ∧
    -- (c) item 1
    (StrictMonoOn (fun x => valueFormula x θ.l₁ θ.l₂ θ.μ θ.lam θ.δ) (Set.Ioo 0 1) ∧
      StrictAntiOn (fun m => valueFormula θ.p₁ θ.l₁ θ.l₂ m θ.lam θ.δ) (Set.Ioo θ.δ θ.lam) ∧
      StrictMonoOn (fun s => valueFormula θ.p₁ θ.l₁ θ.l₂ θ.μ θ.lam s) (Set.Ioo 0 (min θ.μ 1)) ∧
      (∀ a b a' b' : ℝ, b - a = b' - a' →
        valueFormula θ.p₁ a b θ.μ θ.lam θ.δ = valueFormula θ.p₁ a' b' θ.μ θ.lam θ.δ) ∧
      (∀ a b a' b' : ℝ, 0 < b - a → b - a < b' - a' →
        valueFormula θ.p₁ a b θ.μ θ.lam θ.δ < valueFormula θ.p₁ a' b' θ.μ θ.lam θ.δ)) ∧
    -- (d) item 2
    (StrictAntiOn (fun x => valueFormula θ.p₁ θ.l₁ θ.l₂ θ.μ (1 / x) θ.δ) (Set.Ioo 0 (1 / θ.μ)) ∧
      StrictAntiOn (fun x => marginalBenefit θ.p₁ θ.l₁ θ.l₂ θ.μ θ.δ x) (Set.Ioo 0 (1 / θ.μ)) ∧
      StrictMonoOn (fun x => marginalBenefit x θ.l₁ θ.l₂ θ.μ θ.δ (1 / θ.lam)) (Set.Ioo 0 1) ∧
      (∀ a b a' b' : ℝ, b - a = b' - a' →
        marginalBenefit θ.p₁ a b θ.μ θ.δ (1 / θ.lam) =
          marginalBenefit θ.p₁ a' b' θ.μ θ.δ (1 / θ.lam)) ∧
      (∀ a b a' b' : ℝ, 0 < b - a → b - a < b' - a' →
        marginalBenefit θ.p₁ a b θ.μ θ.δ (1 / θ.lam) <
          marginalBenefit θ.p₁ a' b' θ.μ θ.δ (1 / θ.lam)) ∧
      StrictAntiOn (fun m => marginalBenefit θ.p₁ θ.l₁ θ.l₂ m θ.δ (1 / θ.lam))
        (Set.Ioo θ.δ θ.lam) ∧
      StrictMonoOn (fun s => marginalBenefit θ.p₁ θ.l₁ θ.l₂ θ.μ s (1 / θ.lam))
        (Set.Ioo 0 (min θ.μ 1))) := by sorry

end DynTradeFinance
