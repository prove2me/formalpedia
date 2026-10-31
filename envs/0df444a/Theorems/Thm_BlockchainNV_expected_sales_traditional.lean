-- Prove2me | Theorems.Thm_BlockchainNV_expected_sales_traditional
-- name    : BlockchainNV.expected_sales_traditional
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:11.715118+00:00
-- url     : https://prove2.me/theorems/a8a7898f-4229-497b-ac5d-7b7db131de44
-- title:
--   Proof of Theorem 1, Case 2 — expected sales $\mathbb E[\min\{D,q^*_o\}]=\lambda+\beta\mu_X+\sigma_D[(1-r)z^*-\varphi(z^*)]$
-- statement:
--   Assume the base model, let $r = (p-w)/(p-s)$, $z^* = \Phi^{-1}(r)$, $\sigma_D = \sqrt{\beta^2\sigma_X^2 + \sigma^2}$, and let $\varphi$ be the standard normal density. With $D = \lambda + \beta X + \varepsilon$ and $q^*_o = \lambda + \beta\mu_X + \sigma_D z^*$, the traditional retailer's expected sales are
--
--   $$
--   \mathbb E[\min\{D, q^*_o\}] = \lambda + \beta\mu_X + \sigma_D\big[(1-r)z^* - \varphi(z^*)\big].
--   $$
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 2, p.ec11 (PDF p.39)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 2, p.ec11 (PDF p.39). With `D = λ + βX + ε`,
`σ_D = √(β²σ_X² + σ²)`, `q*_o = λ + βµ_X + σ_D z*`, `r = (p − w)/(p − s)` and `z* = Φ^{-1}(r)`:
`E[min{D, q*_o}] = λ + βµ_X + σ_D[(1 − r)z* − φ(z*)]`.

**Formalization Note.** `z* = Φ^{-1}(r)` is a real `z` with `Φ(z) = r`; `φ = gaussianPDFReal 0 1`.
The expectation is the integral over `(Ω, P)` carrying `X` and `ε`. -/
theorem expected_sales_traditional (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) :
    let σD : ℝ := Real.sqrt (θ.beta ^ 2 * θ.sigmaX ^ 2 + θ.sigma ^ 2)
    ∫ ω, min (θ.lam + θ.beta * X ω + ε ω) (θ.lam + θ.beta * θ.muX + σD * z) ∂P =
      θ.lam + θ.beta * θ.muX +
        σD * ((1 - (θ.p - θ.w) / (θ.p - θ.s)) * z - gaussianPDFReal 0 1 z) := by sorry

end BlockchainNV
