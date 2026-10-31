-- Prove2me | Theorems.Thm_CommodityCPC_lemma_2_a
-- name    : CommodityCPC.lemma_2_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:38.284528+00:00
-- url     : https://prove2.me/theorems/23d8e79d-09d6-467e-ae0d-bd6e8ac8f4e4
-- title:
--   Lemma 2(a) — the unique Bayesian Nash equilibrium of the FF subgame, eq. (1)
-- statement:
--   In the FF subgame, where both firms hold the fixed-price contract, the profile
--
--   $$
--   q^{FF}_i=\frac{a-w}{2+\gamma}+[2-\gamma\lambda_j(1+\beta)]\kappa\lambda_if_i,\qquad i\neq j,
--   $$
--
--   is a Bayesian Nash equilibrium, and every Bayesian Nash equilibrium plays these quantities almost surely.
--
--   This is the benchmark without cost-side updating. The deviations range over all admissible strategies, so the claim includes the optimality of an affine strategy among non-affine ones.
--
--   Differences from the source:
--   - encoding: jointly distributed normal noises on an unnamed probability space → the product of four standard normals on ℝ⁴, with the noises as explicit linear forms in the coordinates; reason: this realizes exactly the stated joint law, and every quantity in the statement depends only on that law
--   - reading: ε_A and ε_B are independent of ε_a and ε_s and correlated with coefficient η (p. 9) → the pair (ε_A, ε_B) is bivariate normal and independent of the pair (ε_a, ε_s), all four jointly Gaussian; reason: the sentence leaves the joint law open, and E[f_j | f_i] in Lemma 1 requires joint normality; this is the reading under which the paper's formulas hold
--   - reading: order quantities; standard deviations "sufficiently smaller" than a and µ_s, making negative values negligible (p. 9) → strategies take arbitrary real values and the remark is not encoded; reason: the affine strategies of Lemma 2 are negative with positive probability under Gaussian signals, so a nonnegativity constraint would contradict Lemma 2, and the remark has no formal content
--   - generalization: a and w are a market size and prices → a and w are arbitrary real numbers; reason: no argument uses their sign, and positive values are a special case
--   - encoding: firm i solves max E[π_i | f_i] (p. 10) → no admissible unilateral deviation raises the ex ante expectation E[π_i], among measurable strategies with q(f_i) square integrable; reason: for square-integrable strategies the ex ante and the interim conditions agree up to null sets
--   - encoding: a unique Bayesian Nash equilibrium → every equilibrium satisfies σ_i(f_i) = q_i(f_i) P-almost surely; reason: two strategies that differ on a Lebesgue-null set of signals are the same equilibrium; every payoff depends only on the almost sure class
--   - encoding: θ = σ_s/σ_a, the ratio of two standard deviations, with σ_s the standard deviation of a nondegenerate normal correlated ρ with ε_a (p. 9, p. 11) → θ is a real argument with hypothesis 0 < θ, and σ_s := θσ_a; reason: the paper's θ is positive (σ_s > 0 is implied by the correlation coefficient ρ of (ε_a, ε_s)); the hypothesis excludes only parameters the paper does not have
-- source:
--   Xing–Liu–Zhang–Zhao, SSRN 4717149 (2023-12-27), Lemma 2(a), eq. (1), p. 12; version of record: Management Science (2024), doi:10.1287/mnsc.2023.00304

import Mathlib
import Definitions.Def_CommodityCPC_Model

namespace CommodityCPC

open MeasureTheory

/-- **Lemma 2(a): the unique equilibrium of the FF subgame**, Xing–Liu–Zhang–Zhao, *The Bright Side
of Price Volatility in Global Commodity Procurement*, SSRN 4717149 (2023-12-27), Management
Science (2024), doi:10.1287/mnsc.2023.00304, Lemma 2(a), eq. (1), p. 12. The profile
`q_i = (a − w)/(2 + γ) + [2 − γλ_j(1 + β)]κλ_i f_i` is a Bayesian Nash equilibrium of the FF
subgame, and every equilibrium plays these quantities.

**Formalization Note.** Uniqueness is `P`-almost sure on the quantities `σ i (f_i)`: as functions
on `ℝ`, two equilibrium strategies may differ on a Lebesgue-null set. Strategies are unrestricted
in sign. -/
theorem lemma_2_a (p : Params) {θ : ℝ} (hθ : 0 < θ) :
    (p.game θ FF).IsBNE (fun i x =>
      (p.a - p.w) / (2 + p.γ) + (2 - p.γ * p.lam i.other * (1 + p.β)) * p.κ * p.lam i * x) ∧
    ∀ σ, (p.game θ FF).IsBNE σ → ∀ i,
      (fun ω => σ i (p.signal i ω)) =ᵐ[P] fun ω =>
        (p.a - p.w) / (2 + p.γ) +
          (2 - p.γ * p.lam i.other * (1 + p.β)) * p.κ * p.lam i * p.signal i ω := by sorry

end CommodityCPC
