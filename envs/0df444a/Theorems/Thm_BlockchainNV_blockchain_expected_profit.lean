-- Prove2me | Theorems.Thm_BlockchainNV_blockchain_expected_profit
-- name    : BlockchainNV.blockchain_expected_profit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:13.147187+00:00
-- url     : https://prove2.me/theorems/947de980-ed1c-4353-b11e-2af42f5185b9
-- title:
--   Proof of Theorem 1, Case 1 — $\mathbb E_X[\Pi^*(X)]=(p-w)(\lambda+\beta\mu_X)-(p-s)\sigma\varphi(z^*)$
-- statement:
--   Assume the base model, let $r = (p-w)/(p-s)$, $z^* = \Phi^{-1}(r)$, and let $\varphi$ be the standard normal density. The expected profit of the blockchain retailer, who observes the freshness state $X$ before ordering and then earns $\Pi^*(X)$, is
--
--   $$
--   \mathbb E_X[\Pi^*(X)] = (p-w)(\lambda + \beta\mu_X) - (p-s)\,\sigma\,\varphi(z^*).
--   $$
--
--   This closes Case 1 of the proof of Theorem 1 and is the first clause of the theorem.
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - reading: the optimal order quantity / optimal expected profit, range of q unstated → maximum and supremum over all order quantities q ∈ ℝ; reason: the base model of §2 restricts neither q nor demand to be nonnegative (normal demand), and q*(x) = λ + βx + σz* is negative for small x; nonnegative demand appears only in the §5 extensions.
--   - encoding: the demand distribution conditional on X = x, D_x ∼ N(λ + βx, σ²) → the law of ω ↦ λ + βx + ε(ω) under P; reason: X and ε are independent, so the conditional law of D = λ + βX + ε given X = x is the law of λ + βx + ε.
--   - encoding: E_X[Π*(X)] → ∫ ω, PiStar θ P ε (X ω) ∂P with PiStar an sSup over q ∈ ℝ; reason: the expectation over X of the conditional optimum; the integral over Ω equals the expectation over the law of X.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 1, p.ec11 (PDF p.39)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel
import Definitions.Def_BlockchainNV_PiStar

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, Case 1, p.ec11 (PDF p.39). The expected profit of the
blockchain retailer is `E_X[Π*(X)] = (p − w)(λ + βµ_X) − (p − s)σφ(z*)`.

**Formalization Note.** `E_X[Π*(X)]` is the integral of `ω ↦ Π*(X ω)` over `(Ω, P)`, with
`Π*` the `sSup` definition `PiStar`; `z* = Φ^{-1}(r)` is a real `z` with
`Φ(z) = (p − w)/(p − s)`; `φ = gaussianPDFReal 0 1`. -/
theorem blockchain_expected_profit (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) :
    ∫ ω, PiStar θ P ε (X ω) ∂P =
      (θ.p - θ.w) * (θ.lam + θ.beta * θ.muX) - (θ.p - θ.s) * θ.sigma * gaussianPDFReal 0 1 z := by sorry

end BlockchainNV
