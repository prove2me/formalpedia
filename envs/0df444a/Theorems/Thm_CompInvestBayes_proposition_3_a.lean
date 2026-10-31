-- Prove2me | Theorems.Thm_CompInvestBayes_proposition_3_a
-- name    : CompInvestBayes.proposition_3_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:40.320215+00:00
-- url     : https://prove2.me/theorems/6db45398-db99-46da-9409-871ecafd53a2
-- title:
--   Proposition 3(a) — as $\sigma\to\infty$, $c_2\lambda-\ell^*=o(\sigma^{-1})$ and $h^*-c_2\lambda=o(\sigma^{-1})$
-- statement:
--   Let the standing assumptions hold and $S_1>\mu_L$. Let $\ell(\sigma),h(\sigma)$ be optimal thresholds for every volatility $\sigma>0$, all other parameters and the probability space fixed. Then
--
--   $$
--   \lim_{\sigma\to\infty}\sigma\,\big(c_2\lambda-\ell(\sigma)\big)=0,
--   \qquad
--   \lim_{\sigma\to\infty}\sigma\,\big(h(\sigma)-c_2\lambda\big)=0.
--   $$
--
--   As the leader's earnings become noisy, the follower's waiting region collapses to the kink $c_2\lambda$ of $g$ faster than $1/\sigma$.
--
--   Differences from the source:
--   - encoding: c₂λ − ℓ*(S₁) = o(σ⁻¹) as σ → ∞ → Tendsto (fun σ => σ * (c₂λ − ℓ σ)) atTop (𝓝 0); reason: the paper's o(·) is a ratio tending to 0 (p.12), and the ratio to σ⁻¹ is σ·(c₂λ − ℓ)
--   - generalization: ℓ*(S₁), h*(S₁) of Proposition 2(a) → any choice of optimal thresholds ℓ(σ), h(σ) at each σ > 0; reason: the paper's thresholds are one such choice
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: a probability space with Brownian motions, a binary θ with P(θ = 1) = π₀, Itô integrals, the augmented natural filtration of X^s_1 → the Setup structure (θ = 1{U < y₀} from an independent uniform U), the pathwise integration-by-parts discounted integral discInt, Mathlib's raw natural filtration, stopping times in [0, ∞], F_τ-measurable S₂ ≥ 0; reason: the conventions of the mission's definitions; each realizes the paper's object (see the definitions' Formalization Notes and MODERATION_NOTES.md)
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Proposition 3(a), p.12 (PDF 12); o(·) as defined on p.12

import Mathlib
import Definitions.Def_CompInvestBayes_IsOptimalThresholds

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace CompInvestBayes

/-- **Proposition 3(a)** (SSRN 3408260, p.12, PDF 12). For any leader size `S₁ > µ_L`, the optimal
belief thresholds satisfy, as `σ → ∞`,

`c₂λ − ℓ*(S₁) = o(σ⁻¹)` and `h*(S₁) − c₂λ = o(σ⁻¹)`.

Here `ℓ σ`, `h σ` are optimal thresholds at volatility `σ` (every other parameter and the
probability space fixed), and `o(σ⁻¹)` means the ratio to `σ⁻¹` tends to `0` (p.12). -/
theorem proposition_3_a (p : Params) (hp : p.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (E : Setup Ω) {S1 : ℝ} (hS1 : p.muL < S1)
    (ℓ h : ℝ → ℝ) (hopt : ∀ σ : ℝ, 0 < σ → IsOptimalThresholds p σ E S1 (ℓ σ) (h σ)) :
    Tendsto (fun σ => σ * (p.c2 * p.lam - ℓ σ)) atTop (𝓝 0) ∧
      Tendsto (fun σ => σ * (h σ - p.c2 * p.lam)) atTop (𝓝 0) := by sorry

end CompInvestBayes
