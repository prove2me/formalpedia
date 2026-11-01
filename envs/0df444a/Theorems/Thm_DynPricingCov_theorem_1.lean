-- Prove2me | Theorems.Thm_DynPricingCov_theorem_1
-- name    : DynPricingCov.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:37.590197+00:00
-- url     : https://prove2.me/theorems/62fcdcb9-bede-469c-afa4-4a136af6fc92
-- title:
--   Theorem 1 (corrected: $0\le\underline p$) — UCB pricing has regret at most $4\bar g\bar p\bar\gamma\sqrt{Td\log\frac{2d+T}{2d}}+\bar p\bar D$
-- statement:
--   Consider the generalized linear demand model with covariates under Assumptions 1, 2 and 3, with nonnegative prices, $0\le\underline p$. Let $d\ge1$, $T\ge1$ and let $x_1,\dots,x_T\in\mathcal X$ be **any** covariate sequence. Run Algorithm 1 (UCB Pricing) with regularization parameter $\lambda=1$, with any choice of maximizers and non-anticipating prices. Then its regret satisfies
--
--   $$
--   \mathrm{Reg}_T(x_1,\dots,x_T)\ \le\ 4\,\bar g\,\bar p\,\bar\gamma\,\sqrt{T\,d\,\log\Big(\frac{2d+T}{2d}\Big)}+\bar p\bar D,
--   $$
--
--   where
--
--   $$
--   \bar\gamma=2\bar\theta+\frac{2\bar\sigma}{\underline g}\sqrt{2\log T+2d\log\Big(\frac{2d+T}{2d}\Big)}
--   $$
--
--   bounds the confidence volume. The bound is $\tilde O(d\sqrt T)$, holds without any statistical assumption on the covariates, and does not involve the inverse minimum eigenvalue of a covariate covariance matrix.
--
--   **Formalization Note** The covariates are a deterministic sequence, the run is a relation on processes (any maximizers), the prices are $\mathcal F_{t-1}$-measurable, and the regret is the Bochner integral of the summed realized revenue $\sum_tp_tD_t$ subtracted from $\sum_tr^*(a_t^*,b_t^*)$.
--
--   Differences from the source:
--   - correction: Assumption 1(b): prices in a range [p̲, p̄], p̲ any real → 0 ≤ p̲; reason: the printed statement is false for negative prices: d = T = 1, 𝒳 = {1/√101}, p̲ = −10, p̄ = 1, g(u) = u (g̲ = ḡ = 1), θ̄ = 1, D̄ = 1, σ̄ = 0.01, ε ≡ 0, θ* = −θ₁ with θ₁ = (−10, 100)/√10100 satisfies Assumptions 1–3, Algorithm 1 picks θ₁ and p₁ = −10, and the regret is 10.0 > 6.14 = the Theorem 1 bound (and > 4.04 = 2ḡp̄γ̄‖z₁‖ of the single-period display); the proof's step ≤ ḡp̄|zₜᵀ(θₜ − θ*)| needs |pₜ| ≤ p̄; every price range in the paper is nonnegative
--   - reading: quasi-likelihood (2), lₜ(θ) = −∫_{Dₜ}^{g(zₜᵀθ)} (u − Dₜ)/h(u) du with h = g′∘g⁻¹ → integrated form ℓₜ(θ) = Dₜ·zₜᵀθ − ∫₀^{zₜᵀθ} g(s) ds; reason: substituting u = g(s) shows lₜ − ℓₜ depends on Dₜ only, so (3) has the same maximizers; ℓₜ is defined even when Dₜ is outside the range of g, where (2) needs g⁻¹(Dₜ)
--   - reading: any sequence {xₜ}ₜ₌₁,…,T, with Regπ_T(x₁, …, x_T) a function of that sequence, the expectation taken over the shocks and π only, and x₁, …, xₜ₊₁ listed in ℋₜ → x : ℕ → Fin d → ℝ a deterministic sequence, arbitrary (in 𝒳 on periods 1..T); reason: ℋₜ could suggest random covariates, but r*(a*ₜ, b*ₜ) sits outside the expectation and p.5 says "no expectation is taken for xₜ's in the regret definition" and seeks a bound "over all possible xₜ's", so the claim is for each fixed sequence; every sequence is covered, and the shock process may depend on it
--   - generalization: Assumption 2: g has a bounded derivative over its domain, with g̲ ≤ g′ ≤ ḡ on Z → g : ℝ → ℝ strictly increasing and differentiable on ℝ, g̲ ≤ g′ ≤ ḡ on Z only; reason: the "Specifically" clause pins the bounds to Z and the proof uses g′ only on Z; the paper uses g on all of ℝ (h(u) = g′(g⁻¹(u)) for u ∈ ℝ, p.5), so every g of the source satisfies the Lean hypothesis
--   - generalization: conditioning on the history ℋₜ₋₁ = σ(p₁..pₜ₋₁, ε₁..εₜ₋₁, x₁..xₜ) → any filtration ℱ with εₜ ℱₜ-measurable, pₜ ℱₜ₋₁-measurable, E[εₜ | ℱₜ₋₁] = 0 and the σ̄² conditional MGF bound given ℱₜ₋₁; reason: the paper's ℋ is such a filtration (an admissible policy's pₜ is ℋₜ₋₁-measurable; xₜ is deterministic), so the source's statement is an instance
--   - generalization: θ̂ₜ, (αₜ, βₜ), pₜ := arg max → any maximizers (maximality predicates), any tie-breaking; reason: every tie-breaking rule the source may intend is an instance
--   - encoding: θ = (α, β) ∈ ℝ^{2d}, Assumption 3's conditional log-MGF bound, r* as a max, d and T, "= Õ(d√T)" → Fin (d + d) → ℝ with Fin.append; HasCondSubgaussianMGF with variance proxy σ̄² (integrability of e^{sεₜ} included); StandardBorelSpace Ω; σ̄ > 0; r* as sSup over the compact price interval; 1 ≤ d, 1 ≤ T; the Õ gloss omitted; reason: Lean conventions that change no instance of the source: the conditional MGF bound already makes e^{sεₜ} integrable, the paper divides by σ̄, the max is attained, and Õ(d√T) is implied by the explicit bound
-- source:
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, Theorem 1, p.7 (proof pp.27–28)

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_DynPricingCov_Model
import Definitions.Def_DynPricingCov_UCBPricing

open MeasureTheory ProbabilityTheory

namespace DynPricingCov

/-- **Theorem 1**, Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, p.7
(proof pp.27–28): under Assumptions 1, 2 and 3, with any sequence `{x_t}_{t=1,…,T}`, if the
regularization parameter is `λ = 1`, the regret of Algorithm 1 is at most
`4 ḡ p̄ γ̄ √(T d log((2d + T)/(2d))) + p̄ D̄`, where
`γ̄ = 2θ̄ + (2σ̄/g̲) √(2 log T + 2d log((2d + T)/(2d)))`.

**Formalization Note** The covariates are any deterministic sequence in `𝒳`; the run
`(θhat, θalg, p)` is any run of Algorithm 1 with `λ = 1` (any maximizers) whose prices are
non-anticipating (`p t` is `ℱ (t − 1)`-measurable). Prices are nonnegative, `0 ≤ p̲` (a correction:
the printed statement fails for negative prices). `d ≥ 1`, `T ≥ 1`. -/
theorem theorem_1 {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d T : ℕ} (hd : 1 ≤ d) (hT : 1 ≤ T)
    {X : Set (Fin d → ℝ)} {x : ℕ → Fin d → ℝ} (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ X)
    {θbar plo phi Dbar glo ghi σbar : ℝ} {g : ℝ → ℝ} {θstar : Fin (d + d) → ℝ}
    (h1 : Assumption1 X θbar plo phi Dbar g θstar) (h2 : Assumption2 X θbar plo phi glo ghi g)
    (hplo : 0 ≤ plo)
    {ℱ : Filtration ℕ mΩ} {ε : ℕ → Ω → ℝ} (h3 : Assumption3 P ℱ σbar ε)
    {p : ℕ → Ω → ℝ} {θhat θalg : ℕ → Ω → Fin (d + d) → ℝ}
    (hpm : ∀ t ∈ Finset.Icc 1 T, Measurable[ℱ (t - 1)] (p t))
    (hrun : IsUCBRun d T x g θbar plo phi glo σbar θstar ε p 1 θhat θalg) :
    regret P g plo phi θstar x ε p T ≤
      4 * ghi * phi * gammaBar d T θbar σbar glo *
          Real.sqrt (T * d * Real.log ((2 * d + T) / (2 * d))) + phi * Dbar := by sorry

end DynPricingCov
