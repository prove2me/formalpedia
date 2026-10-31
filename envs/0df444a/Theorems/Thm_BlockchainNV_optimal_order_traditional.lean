-- Prove2me | Theorems.Thm_BlockchainNV_optimal_order_traditional
-- name    : BlockchainNV.optimal_order_traditional
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:17.912984+00:00
-- url     : https://prove2.me/theorems/10466f37-83b1-45dc-a372-bc6fd421e59c
-- title:
--   Eq. (4) — the traditional retailer's optimal order quantity $q^*_o=F^{-1}_D(r)=\lambda+\beta\mu_X+\sigma_Dz^*$
-- statement:
--   Assume the base model, let $r = (p-w)/(p-s)$, $z^* = \Phi^{-1}(r)$ and $\sigma_D = \sqrt{\beta^2\sigma_X^2 + \sigma^2}$. The traditional retailer faces the compound demand $D = \lambda + \beta X + \varepsilon$, with distribution function $F_D$. Then
--
--   $$
--   q^*_o = F^{-1}_D(r) = \lambda + \beta\mu_X + \sigma_D z^*,
--   $$
--
--   in the following sense:
--
--   1. $F_D(\lambda + \beta\mu_X + \sigma_D z^*) = r$, and every $t$ with $F_D(t) = r$ equals $\lambda + \beta\mu_X + \sigma_D z^*$;
--   2. $q^*_o$ maximizes her expected profit $G(q)$ over all $q \in \mathbb R$;
--   3. it is the only maximizer.
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - reading: the optimal order quantity / optimal expected profit, range of q unstated → maximum and supremum over all order quantities q ∈ ℝ; reason: the base model of §2 restricts neither q nor demand to be nonnegative (normal demand), and q*(x) = λ + βx + σz* is negative for small x; nonnegative demand appears only in the §5 extensions.
--   - encoding: q*_o = F^{-1}_D(r) → F_D(q*_o) = r and every t with F_D(t) = r equals q*_o, F_D the c.d.f. of the law of λ + βX + ε under P; reason: F_D is continuous and strictly increasing, so this is the quantile identity.
--   - reading: her optimal order quantity equals q*_o → q*_o maximizes the expected profit over q ∈ ℝ and is its only maximizer; reason: the optimal quantity is a maximizer, and the page names it as the unique one.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, eq. (4), p.8 (PDF p.8); proof of Theorem 1, Case 2, p.ec11 (PDF p.39)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel
import Definitions.Def_BlockchainNV_tradExpProfit

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, eq. (4), p.8 (PDF p.8); also proof of Theorem 1, Case 2, p.ec11 (PDF p.39).
The traditional retailer faces `D = λ + βX + ε ∼ N(λ + βµ_X, β²σ_X² + σ²)`, and her optimal order
quantity is `q*_o = F_D^{-1}(r) = λ + βµ_X + σ_D z*`, where `F_D` is the c.d.f. of `D`,
`σ_D = √(β²σ_X² + σ²)`, `r = (p − w)/(p − s)` and `z* = Φ^{-1}(r)`.

Clauses: (i) `F_D(q*_o) = r` and every `t` with `F_D(t) = r` equals `q*_o` (so
`q*_o = F_D^{-1}(r)`); (ii) `q*_o` maximizes her expected profit over all `q ∈ ℝ`, and (iii) it is
the only maximizer.

**Formalization Note.** `z* = Φ^{-1}(r)` is a real `z` with `Φ(z) = r`. `F_D` is the c.d.f. of
the law of `ω ↦ λ + βX(ω) + ε(ω)` under `P`. -/
theorem optimal_order_traditional (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) :
    let σD : ℝ := Real.sqrt (θ.beta ^ 2 * θ.sigmaX ^ 2 + θ.sigma ^ 2)
    (cdf (P.map fun ω => θ.lam + θ.beta * X ω + ε ω) (θ.lam + θ.beta * θ.muX + σD * z) =
        (θ.p - θ.w) / (θ.p - θ.s) ∧
      ∀ t : ℝ, cdf (P.map fun ω => θ.lam + θ.beta * X ω + ε ω) t = (θ.p - θ.w) / (θ.p - θ.s) →
        t = θ.lam + θ.beta * θ.muX + σD * z) ∧
    (∀ q : ℝ, tradExpProfit θ P X ε q ≤ tradExpProfit θ P X ε (θ.lam + θ.beta * θ.muX + σD * z)) ∧
    (∀ q : ℝ, tradExpProfit θ P X ε q = tradExpProfit θ P X ε (θ.lam + θ.beta * θ.muX + σD * z) →
        q = θ.lam + θ.beta * θ.muX + σD * z) := by sorry

end BlockchainNV
