-- Prove2me | Theorems.Thm_CommodityCPC_eq_6
-- name    : CommodityCPC.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:40.490202+00:00
-- url     : https://prove2.me/theorems/e2a6bfca-dc1a-4ae9-98c7-0aae913fae1a
-- title:
--   Eq. (6) — the ex ante profit of each firm in the CC subgame
-- statement:
--   At every Bayesian Nash equilibrium of the CC subgame, the ex ante profit of firm $i$ with rival $j$ is
--
--   $$
--   \Pi^{CC}_i=\frac{(a-\mu_s)^2}{(2+\gamma)^2}+(1-\rho\theta)^2[2-\gamma\lambda_j(1+\beta)]^2\kappa^2\lambda_i\sigma_a^2.
--   $$
--
--   The first term is the efficiency component and the second the information benefit. Only the factor $(1-\rho\theta)^2$ depends on $\theta$, which is what Proposition 1(a) reads off.
--
--   Differences from the source:
--   - encoding: jointly distributed normal noises on an unnamed probability space → the product of four standard normals on ℝ⁴, with the noises as explicit linear forms in the coordinates; reason: this realizes exactly the stated joint law, and every quantity in the statement depends only on that law
--   - reading: ε_A and ε_B are independent of ε_a and ε_s and correlated with coefficient η (p. 9) → the pair (ε_A, ε_B) is bivariate normal and independent of the pair (ε_a, ε_s), all four jointly Gaussian; reason: the sentence leaves the joint law open, and E[f_j | f_i] in Lemma 1 requires joint normality; this is the reading under which the paper's formulas hold
--   - reading: order quantities; standard deviations "sufficiently smaller" than a and µ_s, making negative values negligible (p. 9) → strategies take arbitrary real values and the remark is not encoded; reason: the affine strategies of Lemma 2 are negative with positive probability under Gaussian signals, so a nonnegativity constraint would contradict Lemma 2, and the remark has no formal content
--   - generalization: a and µ_s are a market size and prices → a and µ_s are arbitrary real numbers; reason: no argument uses their sign, and positive values are a special case
--   - encoding: firm i solves max E[π_i | f_i] (p. 10) → no admissible unilateral deviation raises the ex ante expectation E[π_i], among measurable strategies with q(f_i) square integrable; reason: for square-integrable strategies the ex ante and the interim conditions agree up to null sets
--   - encoding: Π^k_i, the equilibrium ex ante profit → the integral of the realized profit at an arbitrary equilibrium profile σ; reason: Lemma 2 makes the equilibrium unique up to null sets, so the integral does not depend on the chosen σ
--   - encoding: θ = σ_s/σ_a, the ratio of two standard deviations, with σ_s the standard deviation of a nondegenerate normal correlated ρ with ε_a (p. 9, p. 11) → θ is a real argument with hypothesis 0 < θ, and σ_s := θσ_a; reason: the paper's θ is positive (σ_s > 0 is implied by the correlation coefficient ρ of (ε_a, ε_s)); the hypothesis excludes only parameters the paper does not have
-- source:
--   Xing–Liu–Zhang–Zhao, SSRN 4717149 (2023-12-27), §4.2, eq. (6), p. 14; version of record: Management Science (2024), doi:10.1287/mnsc.2023.00304

import Mathlib
import Definitions.Def_CommodityCPC_Model

namespace CommodityCPC

/-- **Eq. (6): the ex ante profit in the CC subgame**, Xing–Liu–Zhang–Zhao, *The Bright Side of
Price Volatility in Global Commodity Procurement*, SSRN 4717149 (2023-12-27), Management Science
(2024), doi:10.1287/mnsc.2023.00304, §4.2, eq. (6), p. 14. At every Bayesian Nash equilibrium `σ`
of the CC subgame, for a firm `i` with rival `j`,
`Π^CC_i = (a − μ_s)²/(2 + γ)² + (1 − ρθ)²[2 − γλ_j(1 + β)]²κ²λ_iσ_a²`.

**Formalization Note.** `Π` is the integral of the realized profit at `σ`, not this formula. -/
theorem eq_6 (p : Params) {θ : ℝ} (hθ : 0 < θ) (σ : Firm → ℝ → ℝ)
    (hσ : (p.game θ CC).IsBNE σ) (i : Firm) :
    p.exAnteProfit θ CC i σ =
      (p.a - p.μs) ^ 2 / (2 + p.γ) ^ 2 +
        (1 - p.ρ * θ) ^ 2 * (2 - p.γ * p.lam i.other * (1 + p.β)) ^ 2 * p.κ ^ 2 * p.lam i *
          p.σa ^ 2 := by sorry

end CommodityCPC
