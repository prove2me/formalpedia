-- Prove2me | Theorems.Thm_BlockchainNV_optimal_order_blockchain
-- name    : BlockchainNV.optimal_order_blockchain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:32.056079+00:00
-- url     : https://prove2.me/theorems/021c7c01-ff2d-4a10-9b6d-be0e65bb5db5
-- title:
--   Eq. (2) — the blockchain retailer's optimal order quantity $q^*(x)=F^{-1}_{D_x}(r)=\lambda+\beta x+\sigma z^*$
-- statement:
--   Assume the base model: parameters with $w>0$, $p>w$, $s<w$, $\lambda>0$, $\beta>0$, $\sigma_X>0$, $\sigma>0$, and independent $X \sim N(\mu_X,\sigma_X^2)$, $\varepsilon \sim N(0,\sigma^2)$. Let $r = (p-w)/(p-s)$ be the critical ratio and $z^* = \Phi^{-1}(r)$ the safety factor. Fix a realized freshness state $x \in \mathbb R$, so that the blockchain retailer's demand is $D_x = \lambda + \beta x + \varepsilon$, with distribution function $F_{D_x}$. Then
--
--   $$
--   q^*(x) = F^{-1}_{D_x}(r) = \lambda + \beta x + \sigma z^*,
--   $$
--
--   in the following sense:
--
--   1. $F_{D_x}(\lambda + \beta x + \sigma z^*) = r$, and every $t$ with $F_{D_x}(t) = r$ equals $\lambda + \beta x + \sigma z^*$;
--   2. $q^*(x)$ maximizes her expected profit $G_x(q)$ over all $q \in \mathbb R$;
--   3. it is the only maximizer.
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - reading: the optimal order quantity / optimal expected profit, range of q unstated → maximum and supremum over all order quantities q ∈ ℝ; reason: the base model of §2 restricts neither q nor demand to be nonnegative (normal demand), and q*(x) = λ + βx + σz* is negative for small x; nonnegative demand appears only in the §5 extensions.
--   - encoding: the demand distribution conditional on X = x, D_x ∼ N(λ + βx, σ²) → the law of ω ↦ λ + βx + ε(ω) under P; reason: X and ε are independent, so the conditional law of D = λ + βX + ε given X = x is the law of λ + βx + ε.
--   - encoding: q*(x) = F^{-1}_{D_x}(r) → F_{D_x}(q*(x)) = r and every t with F_{D_x}(t) = r equals q*(x); reason: F_{D_x} is continuous and strictly increasing, so this is the quantile identity.
--   - reading: the blockchain retailer's optimal order quantity is q*(x) → q*(x) maximizes the expected profit over q ∈ ℝ and is its only maximizer; reason: the definite article names the optimal quantity, so it is a maximizer and the unique one.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, eq. (2), p.8 (PDF p.8); proof of Theorem 1, Case 1, p.ec11 (PDF p.39)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel
import Definitions.Def_BlockchainNV_condExpProfit

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, eq. (2), p.8 (PDF p.8); also proof of Theorem 1, Case 1, p.ec11 (PDF p.39).
Given `X = x`, the blockchain retailer's demand is `D_x = λ + βx + ε ∼ N(λ + βx, σ²)`, and her
optimal order quantity is `q*(x) = F_{D_x}^{-1}(r) = λ + βx + σz*`, where `F_{D_x}` is the c.d.f.
of `D_x`, `r = (p − w)/(p − s)` is the critical ratio and `z* = Φ^{-1}(r)`.

Clauses: (i) `F_{D_x}(λ + βx + σz*) = r` and every `t` with `F_{D_x}(t) = r` equals
`λ + βx + σz*` (so `λ + βx + σz* = F_{D_x}^{-1}(r)`); (ii) `q*(x)` maximizes the expected profit
over all `q ∈ ℝ`, and (iii) it is the only maximizer.

**Formalization Note.** `z* = Φ^{-1}(r)` is encoded as a real `z` with `Φ(z) = r`, which
determines `z` since `Φ` is a strictly increasing bijection `ℝ → (0,1)` and `r ∈ (0,1)`.
`F_{D_x}` is the c.d.f. of the law of `ω ↦ λ + βx + ε(ω)` under `P`. -/
theorem optimal_order_blockchain (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) (x : ℝ) :
    (cdf (P.map fun ω => θ.lam + θ.beta * x + ε ω) (θ.lam + θ.beta * x + θ.sigma * z) =
        (θ.p - θ.w) / (θ.p - θ.s) ∧
      ∀ t : ℝ, cdf (P.map fun ω => θ.lam + θ.beta * x + ε ω) t = (θ.p - θ.w) / (θ.p - θ.s) →
        t = θ.lam + θ.beta * x + θ.sigma * z) ∧
    (∀ q : ℝ, condExpProfit θ P ε x q ≤
        condExpProfit θ P ε x (θ.lam + θ.beta * x + θ.sigma * z)) ∧
    (∀ q : ℝ, condExpProfit θ P ε x q =
        condExpProfit θ P ε x (θ.lam + θ.beta * x + θ.sigma * z) →
        q = θ.lam + θ.beta * x + θ.sigma * z) := by sorry

end BlockchainNV
