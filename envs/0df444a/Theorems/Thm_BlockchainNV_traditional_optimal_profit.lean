-- Prove2me | Theorems.Thm_BlockchainNV_traditional_optimal_profit
-- name    : BlockchainNV.traditional_optimal_profit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:18.603618+00:00
-- url     : https://prove2.me/theorems/21617a9c-789c-4f5a-9bb6-7a92130d5501
-- title:
--   Proof of Theorem 1 — $\Pi^*_o=(p-w)(\lambda+\beta\mu_X)-(p-s)\sigma_D\varphi(z^*)$
-- statement:
--   Assume the base model, let $r = (p-w)/(p-s)$, $z^* = \Phi^{-1}(r)$, $\sigma_D = \sqrt{\beta^2\sigma_X^2 + \sigma^2}$, and let $\varphi$ be the standard normal density. The traditional retailer's optimal expected profit is
--
--   $$
--   \Pi^*_o = (p-w)(\lambda + \beta\mu_X) - (p-s)\,\sigma_D\,\varphi(z^*).
--   $$
--
--   More precisely:
--
--   1. this value is the largest expected profit $G(q)$ over all order quantities $q \in \mathbb R$ (it is attained);
--   2. $\Pi^*_o = \sup_q G(q)$ equals it.
--
--   This closes Case 2 of the proof of Theorem 1 and is the second clause of the theorem.
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - reading: the optimal order quantity / optimal expected profit, range of q unstated → maximum and supremum over all order quantities q ∈ ℝ; reason: the base model of §2 restricts neither q nor demand to be nonnegative (normal demand), and q*(x) = λ + βx + σz* is negative for small x; nonnegative demand appears only in the §5 extensions.
--   - encoding: Π*_o = (p − w)(λ + βµ_X) − (p − s)σ_Dφ(z*) → the value is IsGreatest of the range of q ↦ G(q), and PiStarO (an sSup) equals it; reason: states that the optimum exists and pins the sSup, which is 0 on an unbounded set.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, p.ec12 (PDF p.40); Theorem 1, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel
import Definitions.Def_BlockchainNV_tradExpProfit
import Definitions.Def_BlockchainNV_PiStarO

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, proof of Theorem 1, p.ec12 (PDF p.40). The traditional retailer's optimal expected
profit is `Π*_o = (p − w)(λ + βµ_X) − (p − s)σ_D φ(z*)`, with `σ_D = √(β²σ_X² + σ²)`.

Clauses: the value is the greatest element of the set of her expected profits over all order
quantities `q ∈ ℝ` (the maximum exists and equals it), and `Π*_o` equals it.

**Formalization Note.** `z* = Φ^{-1}(r)` is a real `z` with `Φ(z) = (p − w)/(p − s)`;
`φ = gaussianPDFReal 0 1`; `Π*_o` is `PiStarO` (an `sSup` over `q ∈ ℝ`). -/
theorem traditional_optimal_profit (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) :
    let σD : ℝ := Real.sqrt (θ.beta ^ 2 * θ.sigmaX ^ 2 + θ.sigma ^ 2)
    IsGreatest (Set.range (tradExpProfit θ P X ε))
        ((θ.p - θ.w) * (θ.lam + θ.beta * θ.muX) - (θ.p - θ.s) * σD * gaussianPDFReal 0 1 z) ∧
      PiStarO θ P X ε =
        (θ.p - θ.w) * (θ.lam + θ.beta * θ.muX) - (θ.p - θ.s) * σD * gaussianPDFReal 0 1 z := by sorry

end BlockchainNV
