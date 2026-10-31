-- Prove2me | Theorems.Thm_CommodityCPC_lemma_2_c
-- name    : CommodityCPC.lemma_2_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:27.991812+00:00
-- url     : https://prove2.me/theorems/05a7bc2e-cbfb-46c4-ba80-ee4727586396
-- title:
--   Lemma 2(c) — the unique Bayesian Nash equilibrium of the FC subgame, eqs. (3)–(4), and of the CF subgame
-- statement:
--   In the FC subgame, where firm $A$ holds the fixed-price contract and firm $B$ the contingent-price contract, the profile
--
--   $$
--   q^{FC}_A=\frac{(2-\gamma)a-2w+\gamma\mu_s}{4-\gamma^2}+[2-(1-\rho\theta)\gamma\lambda_B(1+\beta)]\kappa\lambda_Af_A,
--   $$
--
--   $$
--   q^{FC}_B=\frac{(2-\gamma)a-2\mu_s+\gamma w}{4-\gamma^2}+[2(1-\rho\theta)-\gamma\lambda_A(1+\beta)]\kappa\lambda_Bf_B
--   $$
--
--   is a Bayesian Nash equilibrium, and every Bayesian Nash equilibrium plays these quantities almost surely. The same holds in the CF subgame for the profile obtained by exchanging the firms:
--
--   $$
--   q^{CF}_A=\frac{(2-\gamma)a-2\mu_s+\gamma w}{4-\gamma^2}+[2(1-\rho\theta)-\gamma\lambda_B(1+\beta)]\kappa\lambda_Af_A,
--   $$
--
--   $$
--   q^{CF}_B=\frac{(2-\gamma)a-2w+\gamma\mu_s}{4-\gamma^2}+[2-(1-\rho\theta)\gamma\lambda_A(1+\beta)]\kappa\lambda_Bf_B.
--   $$
--
--   With differentiated contracts the two firms may adjust their quantities in opposite directions. The brackets here are the source of the thresholds $\theta^T_A$ and $\theta^T_B$ of Proposition 1(b).
--
--   Differences from the source:
--   - encoding: jointly distributed normal noises on an unnamed probability space → the product of four standard normals on ℝ⁴, with the noises as explicit linear forms in the coordinates; reason: this realizes exactly the stated joint law, and every quantity in the statement depends only on that law
--   - reading: ε_A and ε_B are independent of ε_a and ε_s and correlated with coefficient η (p. 9) → the pair (ε_A, ε_B) is bivariate normal and independent of the pair (ε_a, ε_s), all four jointly Gaussian; reason: the sentence leaves the joint law open, and E[f_j | f_i] in Lemma 1 requires joint normality; this is the reading under which the paper's formulas hold
--   - reading: order quantities; standard deviations "sufficiently smaller" than a and µ_s, making negative values negligible (p. 9) → strategies take arbitrary real values and the remark is not encoded; reason: the affine strategies of Lemma 2 are negative with positive probability under Gaussian signals, so a nonnegativity constraint would contradict Lemma 2, and the remark has no formal content
--   - generalization: a, µ_s and w are a market size and prices → a, µ_s and w are arbitrary real numbers; reason: no argument uses their sign, and positive values are a special case
--   - encoding: firm i solves max E[π_i | f_i] (p. 10) → no admissible unilateral deviation raises the ex ante expectation E[π_i], among measurable strategies with q(f_i) square integrable; reason: for square-integrable strategies the ex ante and the interim conditions agree up to null sets
--   - encoding: a unique Bayesian Nash equilibrium → every equilibrium satisfies σ_i(f_i) = q_i(f_i) P-almost surely; reason: two strategies that differ on a Lebesgue-null set of signals are the same equilibrium; every payoff depends only on the almost sure class
--   - generalization: a unique Bayesian Nash equilibrium for each Cournot subgame, with formulas printed for FF, CC and FC only → the CF subgame is stated too, with the formulas (3)–(4) after exchanging A and B; reason: the paper's sentence covers CF, the model is symmetric under the exchange, and the FC clause is the printed statement
--   - encoding: θ = σ_s/σ_a, the ratio of two standard deviations, with σ_s the standard deviation of a nondegenerate normal correlated ρ with ε_a (p. 9, p. 11) → θ is a real argument with hypothesis 0 < θ, and σ_s := θσ_a; reason: the paper's θ is positive (σ_s > 0 is implied by the correlation coefficient ρ of (ε_a, ε_s)); the hypothesis excludes only parameters the paper does not have
-- source:
--   Xing–Liu–Zhang–Zhao, SSRN 4717149 (2023-12-27), Lemma 2(c), eqs. (3)–(4), p. 12; version of record: Management Science (2024), doi:10.1287/mnsc.2023.00304

import Mathlib
import Definitions.Def_CommodityCPC_Model

namespace CommodityCPC

open MeasureTheory

/-- **Lemma 2(c): the unique equilibrium of the FC subgame, and of the CF subgame**,
Xing–Liu–Zhang–Zhao, *The Bright Side of Price Volatility in Global Commodity Procurement*, SSRN
4717149 (2023-12-27), Management Science (2024), doi:10.1287/mnsc.2023.00304, Lemma 2(c),
eqs. (3)–(4), p. 12. In the FC subgame the profile
`q_A = ((2 − γ)a − 2w + γμ_s)/(4 − γ²) + [2 − (1 − ρθ)γλ_B(1 + β)]κλ_A f_A`,
`q_B = ((2 − γ)a − 2μ_s + γw)/(4 − γ²) + [2(1 − ρθ) − γλ_A(1 + β)]κλ_B f_B`
is a Bayesian Nash equilibrium and every equilibrium plays these quantities. The same holds in the
CF subgame for the profile obtained by exchanging the firms.

**Formalization Note.** The paper's "unique Bayesian Nash equilibrium for each Cournot subgame"
covers CF, for which it prints no formula; the CF formulas are the exchange of `A` and `B` in
(3)–(4). Uniqueness is `P`-almost sure on the quantities. Strategies are unrestricted in sign. -/
theorem lemma_2_c (p : Params) {θ : ℝ} (hθ : 0 < θ) :
    ((p.game θ FC).IsBNE (fun i x =>
        match i with
        | .A => ((2 - p.γ) * p.a - 2 * p.w + p.γ * p.μs) / (4 - p.γ ^ 2) +
            (2 - (1 - p.ρ * θ) * p.γ * p.lam .B * (1 + p.β)) * p.κ * p.lam .A * x
        | .B => ((2 - p.γ) * p.a - 2 * p.μs + p.γ * p.w) / (4 - p.γ ^ 2) +
            (2 * (1 - p.ρ * θ) - p.γ * p.lam .A * (1 + p.β)) * p.κ * p.lam .B * x) ∧
      ∀ σ, (p.game θ FC).IsBNE σ →
        (fun ω => σ .A (p.signal .A ω)) =ᵐ[P] (fun ω =>
          ((2 - p.γ) * p.a - 2 * p.w + p.γ * p.μs) / (4 - p.γ ^ 2) +
            (2 - (1 - p.ρ * θ) * p.γ * p.lam .B * (1 + p.β)) * p.κ * p.lam .A * p.signal .A ω) ∧
        (fun ω => σ .B (p.signal .B ω)) =ᵐ[P] (fun ω =>
          ((2 - p.γ) * p.a - 2 * p.μs + p.γ * p.w) / (4 - p.γ ^ 2) +
            (2 * (1 - p.ρ * θ) - p.γ * p.lam .A * (1 + p.β)) * p.κ * p.lam .B * p.signal .B ω)) ∧
    ((p.game θ CF).IsBNE (fun i x =>
        match i with
        | .A => ((2 - p.γ) * p.a - 2 * p.μs + p.γ * p.w) / (4 - p.γ ^ 2) +
            (2 * (1 - p.ρ * θ) - p.γ * p.lam .B * (1 + p.β)) * p.κ * p.lam .A * x
        | .B => ((2 - p.γ) * p.a - 2 * p.w + p.γ * p.μs) / (4 - p.γ ^ 2) +
            (2 - (1 - p.ρ * θ) * p.γ * p.lam .A * (1 + p.β)) * p.κ * p.lam .B * x) ∧
      ∀ σ, (p.game θ CF).IsBNE σ →
        (fun ω => σ .A (p.signal .A ω)) =ᵐ[P] (fun ω =>
          ((2 - p.γ) * p.a - 2 * p.μs + p.γ * p.w) / (4 - p.γ ^ 2) +
            (2 * (1 - p.ρ * θ) - p.γ * p.lam .B * (1 + p.β)) * p.κ * p.lam .A * p.signal .A ω) ∧
        (fun ω => σ .B (p.signal .B ω)) =ᵐ[P] (fun ω =>
          ((2 - p.γ) * p.a - 2 * p.w + p.γ * p.μs) / (4 - p.γ ^ 2) +
            (2 - (1 - p.ρ * θ) * p.γ * p.lam .A * (1 + p.β)) * p.κ * p.lam .B * p.signal .B ω)) := by sorry

end CommodityCPC
