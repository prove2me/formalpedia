-- Prove2me | Theorems.Thm_BlockchainNV_conditional_optimal_profit
-- name    : BlockchainNV.conditional_optimal_profit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:13.251598+00:00
-- url     : https://prove2.me/theorems/1cbd238a-8299-4fa2-8a9c-ac98ec26987b
-- title:
--   Eq. (3) — $\Pi^*(x)=(p-w)(\lambda+\beta x)-(p-s)\sigma\varphi(z^*)$
-- statement:
--   Assume the base model, let $r = (p-w)/(p-s)$, $z^* = \Phi^{-1}(r)$, and let $\varphi$ be the standard normal density. For every realized freshness state $x$, the blockchain retailer's optimal expected profit conditional on $X = x$ is
--
--   $$
--   \Pi^*(x) = (p-w)(\lambda + \beta x) - (p-s)\,\sigma\,\varphi(z^*).
--   $$
--
--   More precisely:
--
--   1. this value is the largest expected profit $G_x(q)$ over all order quantities $q \in \mathbb R$ (it is attained);
--   2. $\Pi^*(x) = \sup_q G_x(q)$ equals it.
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - reading: the optimal order quantity / optimal expected profit, range of q unstated → maximum and supremum over all order quantities q ∈ ℝ; reason: the base model of §2 restricts neither q nor demand to be nonnegative (normal demand), and q*(x) = λ + βx + σz* is negative for small x; nonnegative demand appears only in the §5 extensions.
--   - encoding: the demand distribution conditional on X = x, D_x ∼ N(λ + βx, σ²) → the law of ω ↦ λ + βx + ε(ω) under P; reason: X and ε are independent, so the conditional law of D = λ + βX + ε given X = x is the law of λ + βx + ε.
--   - encoding: Π*(x) = (p − w)(λ + βx) − (p − s)σφ(z*) → the value is IsGreatest of the range of q ↦ G_x(q), and PiStar (an sSup) equals it; reason: states that the optimum exists and pins the sSup, which is 0 on an unbounded set.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, eq. (3), p.8 (PDF p.8); derivation in the proof of Theorem 1, Case 1, p.ec11 (PDF p.39)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel
import Definitions.Def_BlockchainNV_condExpProfit
import Definitions.Def_BlockchainNV_PiStar

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, eq. (3), p.8 (PDF p.8); derivation p.ec11 (PDF p.39). The blockchain retailer's
optimal expected profit conditional on `X = x` is
`Π*(x) = (p − w)(λ + βx) − (p − s)σφ(z*)`.

Clauses: the value is the greatest element of the set of expected profits over all order
quantities `q ∈ ℝ` (the maximum exists and equals it), and `Π*(x)` equals it.

**Formalization Note.** `z* = Φ^{-1}(r)` is a real `z` with `Φ(z) = (p − w)/(p − s)`;
`φ = gaussianPDFReal 0 1`; `Π*(x)` is `PiStar` (an `sSup` over `q ∈ ℝ`). -/
theorem conditional_optimal_profit (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) (x : ℝ) :
    IsGreatest (Set.range (condExpProfit θ P ε x))
        ((θ.p - θ.w) * (θ.lam + θ.beta * x) - (θ.p - θ.s) * θ.sigma * gaussianPDFReal 0 1 z) ∧
      PiStar θ P ε x =
        (θ.p - θ.w) * (θ.lam + θ.beta * x) - (θ.p - θ.s) * θ.sigma * gaussianPDFReal 0 1 z := by sorry

end BlockchainNV
