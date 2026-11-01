-- Prove2me | Theorems.Thm_DynPricingCov_proposition_1
-- name    : DynPricingCov.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:20.898108+00:00
-- url     : https://prove2.me/theorems/c0e30a02-19b9-4f59-ba1a-4b065dab1068
-- title:
--   Proposition 1 — estimation error of $\hat\theta_t$ in the $M_t$-norm
-- statement:
--   Under Assumptions 1–3, let the prices $p_t\in[\underline p,\bar p]$ be non-anticipating ($p_t$ depends only on the information before period $t$) and let $\hat\theta_t$ be the regularized quasi-likelihood estimator (3) with parameter $\lambda>0$ for $t=1,\dots,T$. Then for every $\delta\in(0,1)$,
--
--   $$
--   \mathbb P\Big(\exists t\in\{1,\dots,T\}:\ \big\|\hat\theta_t-\theta^*\big\|_{M_t}\ \ge\ 2\sqrt\lambda\,\bar\theta+\frac{2\bar\sigma}{\underline g}\sqrt{2\log\frac1\delta+\log\frac{\det M_t}{\lambda^{2d}}}\Big)\le\delta .
--   $$
--
--   The bound measures the estimation error in the geometry of the sampled design matrix $M_t=\lambda I_{2d}+\sum_{t'\le t}z_{t'}z_{t'}^\top$, so it needs no i.i.d. or minimum-eigenvalue assumption on the covariates. It is the basis of the confidence sets of Algorithm 1.
--
--   **Formalization Note** The probability is the outer measure of the event, so $\hat\theta_t$ need not be measurable; $\lambda^{2d}$ is `lam ^ (d + d)`.
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
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, Proposition 1, p.6 (proof pp.26–27)

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_DynPricingCov_Model
import Definitions.Def_DynPricingCov_UCBPricing

open MeasureTheory ProbabilityTheory Matrix

namespace DynPricingCov

/-- **Proposition 1** (Filippi et al. (2010)), Wang, Talluri & Li, On Dynamic Pricing with
Covariates, arXiv:2112.13254v3, p.6 (proof pp.26–27): for any regularization parameter `λ > 0`
and any `δ ∈ (0, 1)`,
`P(∃ t ∈ {1, …, T} : ‖θ̂_t − θ*‖_{M_t} ≥ 2√λ θ̄ + (2σ̄/g̲) √(2 log(1/δ) + log(det M_t / λ^{2d}))) ≤ δ`.

**Formalization Note** The model is Assumptions 1–3 with covariates `x_t ∈ 𝒳`, prices in
`[p̲, p̄]` that are `ℱ (t − 1)`-measurable (non-anticipating), and `θhat t` any maximizer of (3) at
every `t ∈ {1, …, T}` and every outcome. `θhat` need not be measurable: the probability is the
outer measure of the event. `λ^{2d}` is `lam ^ (d + d)`. -/
theorem proposition_1 {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d T : ℕ} (hd : 1 ≤ d) (hT : 1 ≤ T)
    {X : Set (Fin d → ℝ)} {x : ℕ → Fin d → ℝ} (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ X)
    {θbar plo phi Dbar glo ghi σbar : ℝ} {g : ℝ → ℝ} {θstar : Fin (d + d) → ℝ}
    (h1 : Assumption1 X θbar plo phi Dbar g θstar) (h2 : Assumption2 X θbar plo phi glo ghi g)
    {ℱ : Filtration ℕ mΩ} {ε : ℕ → Ω → ℝ} (h3 : Assumption3 P ℱ σbar ε)
    {p : ℕ → Ω → ℝ}
    (hp : ∀ t ∈ Finset.Icc 1 T, Measurable[ℱ (t - 1)] (p t) ∧ ∀ ω, p t ω ∈ Set.Icc plo phi)
    {lam : ℝ} (hlam : 0 < lam) {θhat : ℕ → Ω → Fin (d + d) → ℝ}
    (hθhat : ∀ t ∈ Finset.Icc 1 T, ∀ ω, IsQMLE g glo lam θbar θstar x ε p t ω (θhat t ω))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | ∃ t ∈ Finset.Icc 1 T,
      2 * Real.sqrt lam * θbar + 2 * σbar / glo *
          Real.sqrt (2 * Real.log (1 / δ) + Real.log ((designM lam x p t ω).det / lam ^ (d + d)))
        ≤ mNorm (designM lam x p t ω) (θhat t ω - θstar)} ≤ δ := by sorry

end DynPricingCov
