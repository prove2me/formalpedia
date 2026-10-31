-- Prove2me | Theorems.Thm_BlockchainNV_compound_demand_law
-- name    : BlockchainNV.compound_demand_law
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:09.520201+00:00
-- url     : https://prove2.me/theorems/d22acb39-3838-4979-800b-26cdd38f1519
-- title:
--   Proof of Theorem 1, Case 2 — $D=\lambda+\beta X+\varepsilon\sim N(\lambda+\beta\mu_X,\beta^2\sigma_X^2+\sigma^2)$
-- statement:
--   Assume the base model: $X \sim N(\mu_X, \sigma_X^2)$ and $\varepsilon \sim N(0, \sigma^2)$ are independent. Then the compound demand faced by the traditional retailer is normal:
--
--   $$
--   D = \lambda + \beta X + \varepsilon \sim N\big(\lambda + \beta\mu_X,\ \beta^2\sigma_X^2 + \sigma^2\big).
--   $$
--
--   Independence is what makes the variances add; it is the only place in the proof of Theorem 1 where independence of $X$ and $\varepsilon$ enters.
--
--   Differences from the source:
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - encoding: N(λ + βµ_X, β²σ_X² + σ²) → gaussianReal (λ + βµ_X) (β²σ_X² + σ²).toNNReal; reason: Mathlib's Gaussian takes the variance in ℝ≥0; toNNReal is the identity on a nonnegative number.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 2, p.ec11 (PDF p.39); §2.1, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 2, p.ec11 (PDF p.39); also §2.1, p.8. Since
`X ∼ N(µ_X, σ_X²)` and `ε ∼ N(0, σ²)` are independent,
`D = λ + βX + ε ∼ N(λ + βµ_X, β²σ_X² + σ²)`.

**Formalization Note.** `gaussianReal m v` takes the variance `v : ℝ≥0`; `Real.toNNReal` is the identity
on the nonnegative `β²σ_X² + σ²`. -/
theorem compound_demand_law (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) :
    HasLaw (fun ω => θ.lam + θ.beta * X ω + ε ω)
      (gaussianReal (θ.lam + θ.beta * θ.muX)
        (θ.beta ^ 2 * θ.sigmaX ^ 2 + θ.sigma ^ 2).toNNReal) P := by sorry

end BlockchainNV
