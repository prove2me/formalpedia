-- Prove2me | Theorems.Thm_DynPricingCov_lemma_3
-- name    : DynPricingCov.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:35.413442+00:00
-- url     : https://prove2.me/theorems/66a44124-61a0-4608-8774-4d4f9f8fc73d
-- title:
--   Lemma 3 — $\xi_t(\theta^*)$ is a conditionally zero-mean, $\bar\sigma^2$-sub-Gaussian increment
-- statement:
--   In the generalized linear demand model, let $\xi_t(\theta)=D_t-g(z_t^\top\theta)$ be the residual of period $t$ at parameter $\theta$. Under Assumption 3, for $t=1,\dots,T$,
--
--   $$
--   \mathbb E\big[\xi_t(\theta^*)\mid\mathcal H_{t-1}\big]=0,
--   $$
--
--   and $\xi_t(\theta^*)$ is $\bar\sigma^2$-sub-Gaussian conditionally on $\mathcal H_{t-1}$: $\mathbb E[e^{s\xi_t(\theta^*)}\mid\mathcal H_{t-1}]\le e^{\bar\sigma^2s^2/2}$ for all $s\in\mathbb R$.
--
--   The residuals at the true parameter therefore form a sub-Gaussian martingale difference sequence, which is what the self-normalized bound for the score $S_t=\sum_{t'\le t}\xi_{t'}(\theta^*)z_{t'}/\bar\sigma$ requires.
--
--   **Formalization Note** $\mathcal H_{t-1}$ is $\mathcal F_{t-1}$ for any filtration $\mathcal F$ satisfying Assumption 3; the price process is arbitrary.
--
--   Differences from the source:
--   - reading: any sequence {xₜ}ₜ₌₁,…,T, with Regπ_T(x₁, …, x_T) a function of that sequence, the expectation taken over the shocks and π only, and x₁, …, xₜ₊₁ listed in ℋₜ → x : ℕ → Fin d → ℝ a deterministic sequence, arbitrary (in 𝒳 on periods 1..T); reason: ℋₜ could suggest random covariates, but r*(a*ₜ, b*ₜ) sits outside the expectation and p.5 says "no expectation is taken for xₜ's in the regret definition" and seeks a bound "over all possible xₜ's", so the claim is for each fixed sequence; every sequence is covered, and the shock process may depend on it
--   - generalization: a non-anticipatory pricing policy, under the standing Assumptions 1–3 → any price process, Assumption 3 only; reason: ξₜ(θ*) = εₜ by the definition of Dₜ, so the claim does not involve the prices or Assumptions 1–2; the source's setting is an instance
--   - generalization: conditioning on the history ℋₜ₋₁ = σ(p₁..pₜ₋₁, ε₁..εₜ₋₁, x₁..xₜ) → any filtration ℱ with εₜ ℱₜ-measurable, pₜ ℱₜ₋₁-measurable, E[εₜ | ℱₜ₋₁] = 0 and the σ̄² conditional MGF bound given ℱₜ₋₁; reason: the paper's ℋ is such a filtration (an admissible policy's pₜ is ℋₜ₋₁-measurable; xₜ is deterministic), so the source's statement is an instance
--   - encoding: θ = (α, β) ∈ ℝ^{2d}, zₜ = (xₜ, pₜxₜ), Assumption 3's conditional log-MGF bound, σ̄²-sub-Gaussian → Fin (d + d) → ℝ with θ = Fin.append α β; Mathlib's HasCondSubgaussianMGF with variance proxy σ̄² (which includes integrability of e^{sεₜ}); StandardBorelSpace Ω; σ̄ > 0; reason: Lean conventions; the bound E[e^{sεₜ} | ℋₜ₋₁] ≤ e^{σ̄²s²/2} already makes e^{sεₜ} integrable; the paper divides by σ̄ (Sₜ, p.25), so σ̄ = 0 is an undefined case
-- source:
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, Lemma 3, p.25

import Mathlib
import Definitions.Def_DynPricingCov_Model

open MeasureTheory ProbabilityTheory

namespace DynPricingCov

/-- **Lemma 3**, Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, p.25:
for `t = 1, …, T`, `E[ξ_t(θ*) | ℋ_{t−1}] = 0`, and `ξ_t(θ*) | ℋ_{t−1}` is `σ̄²`-sub-Gaussian, where
`ξ_t(θ) = D_t − g(z_tᵀθ)`.

**Formalization Note** `ℋ` is any filtration `ℱ` satisfying Assumption 3 (in the shifted index
convention of `Assumption3`, `ℋ_{t−1}` is `ℱ (t − 1)`). The price process is arbitrary. -/
theorem lemma_3 {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d T : ℕ} (g : ℝ → ℝ) (θstar : Fin (d + d) → ℝ)
    (x : ℕ → Fin d → ℝ) {ℱ : Filtration ℕ mΩ} {σbar : ℝ} {ε : ℕ → Ω → ℝ}
    (h3 : Assumption3 P ℱ σbar ε) (p : ℕ → Ω → ℝ) {t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    P[xi g θstar x ε p θstar t | ℱ (t - 1)] =ᵐ[P] 0 ∧
      HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1)) (xi g θstar x ε p θstar t)
        (σbar ^ 2).toNNReal P := by sorry

end DynPricingCov
