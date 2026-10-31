-- Prove2me | Theorems.Thm_BlockchainNV_lemma_EC_1
-- name    : BlockchainNV.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:37.900986+00:00
-- url     : https://prove2.me/theorems/45aa0d0e-380d-40c9-a79f-4d28959432fd
-- title:
--   Lemma EC.1 — partial expectations of a normal random variable
-- statement:
--   Let $Y \sim N(\mu, \sigma^2)$ with $\sigma > 0$ and density $f_Y$, let $t \in \mathbb R$, and let $\varphi$ and $\Phi$ be the standard normal density and distribution function. Then
--
--   $$
--   \mathbb E[\min\{Y,t\}] = \int_{-\infty}^{t} y f_Y(y)\,dy + \int_{t}^{+\infty} t f_Y(y)\,dy = t - \sigma\varphi\Big(\frac{t-\mu}{\sigma}\Big) + (\mu - t)\,\Phi\Big(\frac{t-\mu}{\sigma}\Big),
--   $$
--
--   $$
--   \mathbb E[Y \mathbb 1_{\{Y \le t\}}] = \int_{-\infty}^{t} y f_Y(y)\,dy = -\sigma\varphi\Big(\frac{t-\mu}{\sigma}\Big) + \mu\,\Phi\Big(\frac{t-\mu}{\sigma}\Big),
--   $$
--
--   $$
--   \mathbb E[Y \mathbb 1_{\{Y > t\}}] = \int_{t}^{+\infty} y f_Y(y)\,dy = \sigma\varphi\Big(\frac{t-\mu}{\sigma}\Big) + \mu\Big(1 - \Phi\Big(\frac{t-\mu}{\sigma}\Big)\Big).
--   $$
--
--   The first identity gives the expected sales of a newsvendor facing normal demand; the paper uses it in both cases of the proof of Theorem 1.
--
--   **Formalization Note** Each display is stated as two equalities, the expectation equal to the closed form and the integral expression equal to the closed form. Expectations are integrals against the law $N(\mu,\sigma^2)$.
--
--   Differences from the source:
--   - encoding: a random variable Y ∼ N(µ, σ²) → integrals against the law gaussianReal µ (σ²).toNNReal, with f_Y = gaussianPDFReal µ (σ²).toNNReal; reason: each expectation depends only on the law of Y.
--   - encoding: ∫_{−∞}^{t} and ∫_{t}^{+∞} → Lebesgue integrals over (−∞, t] and (t, ∞); reason: the endpoint has Lebesgue measure zero.
--   - reading: Y ∼ N(µ, σ²), positivity of σ not printed → 0 < σ; reason: the right-hand sides divide by σ.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, Lemma EC.1, p.ec10 (PDF p.38)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, Lemma EC.1, p.ec10 (PDF p.38). If `Y ∼ N(µ, σ²)` and `t ∈ ℝ`, with `f_Y` the density
of `Y`, `φ`, `Φ` the standard normal p.d.f. and c.d.f.:
`E[min{Y,t}] = ∫_{−∞}^t y f_Y(y)dy + ∫_t^{+∞} t f_Y(y)dy = t − σφ((t−µ)/σ) + (µ−t)Φ((t−µ)/σ)`,
`E[Y 1{Y ≤ t}] = ∫_{−∞}^t y f_Y(y)dy = −σφ((t−µ)/σ) + µΦ((t−µ)/σ)`,
`E[Y 1{Y > t}] = ∫_t^{+∞} y f_Y(y)dy = σφ((t−µ)/σ) + µ(1 − Φ((t−µ)/σ))`.

**Formalization Note.** The lemma is stated on the law `N(µ, σ²) = gaussianReal µ (σ²).toNNReal`
(variance argument) of `Y`; `E[g(Y)]` is `∫ y, g y ∂N(µ, σ²)`. `f_Y = gaussianPDFReal µ (σ²).toNNReal`,
`φ = gaussianPDFReal 0 1`, `Φ = cdf (gaussianReal 0 1)`. Each line of the display is the pair of
equalities "expectation = closed form" and "integral expression = closed form". `σ > 0` is the
reading under which `(t − µ)/σ` is defined. -/
theorem lemma_EC_1 (μ σ t : ℝ) (hσ : 0 < σ) :
    let N : Measure ℝ := gaussianReal μ (σ ^ 2).toNNReal
    let f : ℝ → ℝ := gaussianPDFReal μ (σ ^ 2).toNNReal
    let φ : ℝ → ℝ := gaussianPDFReal 0 1
    let Φ : ℝ → ℝ := cdf (gaussianReal 0 1)
    ((∫ y, min y t ∂N) = t - σ * φ ((t - μ) / σ) + (μ - t) * Φ ((t - μ) / σ) ∧
      (∫ y in Set.Iic t, y * f y) + (∫ y in Set.Ioi t, t * f y) =
        t - σ * φ ((t - μ) / σ) + (μ - t) * Φ ((t - μ) / σ)) ∧
    ((∫ y, (Set.Iic t).indicator (fun y => y) y ∂N) =
        -σ * φ ((t - μ) / σ) + μ * Φ ((t - μ) / σ) ∧
      (∫ y in Set.Iic t, y * f y) = -σ * φ ((t - μ) / σ) + μ * Φ ((t - μ) / σ)) ∧
    ((∫ y, (Set.Ioi t).indicator (fun y => y) y ∂N) =
        σ * φ ((t - μ) / σ) + μ * (1 - Φ ((t - μ) / σ)) ∧
      (∫ y in Set.Ioi t, y * f y) = σ * φ ((t - μ) / σ) + μ * (1 - Φ ((t - μ) / σ))) := by sorry

end BlockchainNV
