-- Prove2me | Theorems.Thm_DynPricingCov_corollary_1
-- name    : DynPricingCov.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:29.561965+00:00
-- url     : https://prove2.me/theorems/7747ea27-96e8-4e75-b8a2-167f9912897f
-- title:
--   Corollary 1 — the estimation error stays within the explicit radius with probability $\ge1-1/T$
-- statement:
--   Under the hypotheses of Proposition 1 (Assumptions 1–3, non-anticipating prices in $[\underline p,\bar p]$, $\hat\theta_t$ the estimator (3)), for every $\lambda>0$,
--
--   $$
--   \mathbb P\Big(\exists t\in\{1,\dots,T\}:\ \big\|\hat\theta_t-\theta^*\big\|_{M_t}\ \ge\ 2\sqrt\lambda\,\bar\theta+\frac{2\bar\sigma}{\underline g}\sqrt{2\log T+2d\log\frac{2d\lambda+T}{2d\lambda}}\Big)\le\frac1T .
--   $$
--
--   The radius no longer depends on $M_t$; it is the radius of the confidence sets $\Theta_t$ of Algorithm 1, and the event that all of them contain $\theta^*$ is the good event of the regret analysis.
--
--   **Formalization Note** The radius is `radius d T θbar σbar glo lam`; the probability is the outer measure of the event.
--
--   Differences from the source:
--   - reading: quasi-likelihood (2), lₜ(θ) = −∫_{Dₜ}^{g(zₜᵀθ)} (u − Dₜ)/h(u) du with h = g′∘g⁻¹ → integrated form ℓₜ(θ) = Dₜ·zₜᵀθ − ∫₀^{zₜᵀθ} g(s) ds; reason: substituting u = g(s) shows lₜ − ℓₜ depends on Dₜ only, so (3) has the same maximizers; ℓₜ is defined even when Dₜ is outside the range of g, where (2) needs g⁻¹(Dₜ)
--   - reading: any sequence {xₜ}ₜ₌₁,…,T, with Regπ_T(x₁, …, x_T) a function of that sequence, the expectation taken over the shocks and π only, and x₁, …, xₜ₊₁ listed in ℋₜ → x : ℕ → Fin d → ℝ a deterministic sequence, arbitrary (in 𝒳 on periods 1..T); reason: ℋₜ could suggest random covariates, but r*(a*ₜ, b*ₜ) sits outside the expectation and p.5 says "no expectation is taken for xₜ's in the regret definition" and seeks a bound "over all possible xₜ's", so the claim is for each fixed sequence; every sequence is covered, and the shock process may depend on it
--   - generalization: Assumption 2: g has a bounded derivative over its domain, with g̲ ≤ g′ ≤ ḡ on Z → g : ℝ → ℝ strictly increasing and differentiable on ℝ, g̲ ≤ g′ ≤ ḡ on Z only; reason: the "Specifically" clause pins the bounds to Z and the proof uses g′ only on Z; the paper uses g on all of ℝ (h(u) = g′(g⁻¹(u)) for u ∈ ℝ, p.5), so every g of the source satisfies the Lean hypothesis
--   - generalization: conditioning on the history ℋₜ₋₁ = σ(p₁..pₜ₋₁, ε₁..εₜ₋₁, x₁..xₜ) → any filtration ℱ with εₜ ℱₜ-measurable, pₜ ℱₜ₋₁-measurable, E[εₜ | ℱₜ₋₁] = 0 and the σ̄² conditional MGF bound given ℱₜ₋₁; reason: the paper's ℋ is such a filtration (an admissible policy's pₜ is ℋₜ₋₁-measurable; xₜ is deterministic), so the source's statement is an instance
--   - generalization: θ̂ₜ, (αₜ, βₜ), pₜ := arg max → any maximizers (maximality predicates), any tie-breaking; reason: every tie-breaking rule the source may intend is an instance
--   - generalization: P(event) with a (implicitly measurable) estimator θ̂ₜ → P of the event as an outer measure; θ̂ₜ any maximizer of (3), measurable or not; reason: for a measurable θ̂ the event is measurable and the outer measure is its probability
--   - encoding: θ = (α, β) ∈ ℝ^{2d}, zₜ = (xₜ, pₜxₜ), Assumption 3's conditional log-MGF bound, σ̄²-sub-Gaussian → Fin (d + d) → ℝ with θ = Fin.append α β; Mathlib's HasCondSubgaussianMGF with variance proxy σ̄² (which includes integrability of e^{sεₜ}); StandardBorelSpace Ω; σ̄ > 0; reason: Lean conventions; the bound E[e^{sεₜ} | ℋₜ₋₁] ≤ e^{σ̄²s²/2} already makes e^{sεₜ} integrable; the paper divides by σ̄ (Sₜ, p.25), so σ̄ = 0 is an undefined case
--   - encoding: dimension d and horizon T → 1 ≤ d, 1 ≤ T; reason: the bounds contain log T and 2d in a denominator; the source's d, T are positive
-- source:
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, Corollary 1, p.6 (proof p.27)

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_DynPricingCov_Model
import Definitions.Def_DynPricingCov_UCBPricing

open MeasureTheory ProbabilityTheory Matrix

namespace DynPricingCov

/-- **Corollary 1**, Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3,
p.6 (proof p.27): for all `λ > 0`,
`P(∃ t ∈ {1, …, T} : ‖θ̂_t − θ*‖_{M_t} ≥ 2√λ θ̄ + (2σ̄/g̲) √(2 log T + 2d log((2dλ + T)/(2dλ)))) ≤ 1/T`.

**Formalization Note** Same model and hypotheses as `proposition_1`; the radius is `radius d T θbar
σbar glo lam`. The probability is the outer measure of the event (`θhat` need not be measurable). -/
theorem corollary_1 {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d T : ℕ} (hd : 1 ≤ d) (hT : 1 ≤ T)
    {X : Set (Fin d → ℝ)} {x : ℕ → Fin d → ℝ} (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ X)
    {θbar plo phi Dbar glo ghi σbar : ℝ} {g : ℝ → ℝ} {θstar : Fin (d + d) → ℝ}
    (h1 : Assumption1 X θbar plo phi Dbar g θstar) (h2 : Assumption2 X θbar plo phi glo ghi g)
    {ℱ : Filtration ℕ mΩ} {ε : ℕ → Ω → ℝ} (h3 : Assumption3 P ℱ σbar ε)
    {p : ℕ → Ω → ℝ}
    (hp : ∀ t ∈ Finset.Icc 1 T, Measurable[ℱ (t - 1)] (p t) ∧ ∀ ω, p t ω ∈ Set.Icc plo phi)
    {lam : ℝ} (hlam : 0 < lam) {θhat : ℕ → Ω → Fin (d + d) → ℝ}
    (hθhat : ∀ t ∈ Finset.Icc 1 T, ∀ ω, IsQMLE g glo lam θbar θstar x ε p t ω (θhat t ω)) :
    P.real {ω | ∃ t ∈ Finset.Icc 1 T,
      radius d T θbar σbar glo lam ≤ mNorm (designM lam x p t ω) (θhat t ω - θstar)} ≤
      1 / (T : ℝ) := by sorry

end DynPricingCov
