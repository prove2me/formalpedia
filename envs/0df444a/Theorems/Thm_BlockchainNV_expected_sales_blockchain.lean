-- Prove2me | Theorems.Thm_BlockchainNV_expected_sales_blockchain
-- name    : BlockchainNV.expected_sales_blockchain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:06.426729+00:00
-- url     : https://prove2.me/theorems/b799245f-b8cc-406a-a76d-d088d3f5d68c
-- title:
--   Proof of Theorem 1, Case 1 — expected sales $\mathbb E[\min\{D_x,q^*(x)\}]=\lambda+\beta x+\sigma[(1-r)z^*-\varphi(z^*)]$
-- statement:
--   Assume the base model, let $r = (p-w)/(p-s)$, $z^* = \Phi^{-1}(r)$, and let $\varphi$ be the standard normal density. For every realized freshness state $x$, with $D_x = \lambda + \beta x + \varepsilon$ and $q^*(x) = \lambda + \beta x + \sigma z^*$, the blockchain retailer's expected sales are
--
--   $$
--   \mathbb E[\min\{D_x, q^*(x)\}] = \lambda + \beta x + \sigma\big[(1-r)z^* - \varphi(z^*)\big].
--   $$
--
--   This is the step of the proof of Theorem 1 that evaluates the expected sales at the optimal order by Lemma EC.1.
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - encoding: the demand distribution conditional on X = x, D_x ∼ N(λ + βx, σ²) → the law of ω ↦ λ + βx + ε(ω) under P; reason: X and ε are independent, so the conditional law of D = λ + βX + ε given X = x is the law of λ + βx + ε.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 1, p.ec11 (PDF p.39)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 1, p.ec11 (PDF p.39). With `D_x = λ + βx + ε`,
`q*(x) = λ + βx + σz*`, `r = (p − w)/(p − s)` and `z* = Φ^{-1}(r)`, the expected sales are
`E[min{D_x, q*(x)}] = λ + βx + σ[(1 − r)z* − φ(z*)]`.

**Formalization Note.** `z* = Φ^{-1}(r)` is a real `z` with `Φ(z) = r`; `φ = gaussianPDFReal 0 1`.
The expectation is the integral over `(Ω, P)` carrying `ε`. -/
theorem expected_sales_blockchain (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) (x : ℝ) :
    ∫ ω, min (θ.lam + θ.beta * x + ε ω) (θ.lam + θ.beta * x + θ.sigma * z) ∂P =
      θ.lam + θ.beta * x +
        θ.sigma * ((1 - (θ.p - θ.w) / (θ.p - θ.s)) * z - gaussianPDFReal 0 1 z) := by sorry

end BlockchainNV
