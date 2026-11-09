-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_a_4
-- name    : AMPLowDeg.RankOne.lemma_a_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:05:23.512194+00:00
-- url     : https://prove2.me/theorems/f4d714a6-8b5d-4b94-a614-9a7fd4e5c0b7
-- title:
--   Lemma A.4 — conditional moment–cumulant recurrence (A.1)
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$, and let $\theta$ have i.i.d. coordinates with law $\pi$ on a probability space that also carries external randomness $Z$ independent of $\theta$. Let $R=R(\theta,Z)\in\mathbb R^N$ for a measurable map $R$, and let $\mathcal K_\alpha(R)$ be the conditional cumulants (2.7). Then for every $\beta\in\mathbb N_0^{\mathcal E_n}$, almost surely,
--
--   $$
--   \mathbb E[\theta_1x^\beta\mid R]=\sum_{\alpha\le\beta}\binom{\beta}{\alpha}\mathcal K_\alpha(R)\,\mathbb E[x^{\beta-\alpha}\mid R],
--   $$
--
--   where $x^\beta=\prod_e x_e(\theta)^{\beta_e}$, $\alpha\le\beta$ is coordinatewise and $\binom\beta\alpha=\prod_e\binom{\beta_e}{\alpha_e}$.
--
--   The recurrence converts conditional correlations of $\theta_1$ with monomials into conditional cumulants; it yields the identity (3.3) behind Lemma 2.2.
--
--   Differences from the source:
--
--   - generalization: R = R(θ, Z) with Z independent of (θ, W) → Z independent of θ; no noise W on the probability space; reason: W does not occur in (A.1); every setting of the source (Z independent of (θ, W)) satisfies the Lean hypotheses
--   - encoding: external randomness Z → a measurable random element of an arbitrary measurable space, and R = r(θ, Z) for a measurable r; reason: the source leaves the space of Z unspecified
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 22, Lemma A.4, eq. (A.1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma A.4, p. 22 — conditional moment–cumulant recurrence (A.1): for every auxiliary
observation `R = R(θ, Z)` with external randomness `Z` independent of `θ` and every
`β ∈ ℕ₀^{ℰₙ}`, almost surely
`E[θ₁ x^β | R] = Σ_{α ≤ β} (β choose α) 𝒦_α(R) E[x^{β−α} | R]`. -/
theorem lemma_a_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0) (hmom : AllMomentsFinite π)
    (n N : ℕ) (hn : 0 < n) {𝒵 : Type*} [MeasurableSpace 𝒵]
    (θ : Ω → Fin n → ℝ) (Z : Ω → 𝒵) (hθ : Measurable θ) (hZ : Measurable Z)
    (hθlaw : μ.map θ = Measure.pi fun _ : Fin n => π) (hind : IndepFun θ Z μ)
    (rfun : (Fin n → ℝ) × 𝒵 → Fin N → ℝ) (hr : Measurable rfun) (β : Edge n → ℕ) :
    μ[fun w => θ w ⟨0, hn⟩ * ∏ e, (edgeVar (θ w) e) ^ β e |
        MeasurableSpace.comap (fun w => rfun (θ w, Z w)) inferInstance] =ᵐ[μ]
      fun w => ∑ α ∈ Fintype.piFinset (fun e : Edge n => Finset.range (β e + 1)),
        ((∏ e, (β e).choose (α e) : ℕ) : ℝ) *
          Kcum μ θ (fun w' => rfun (θ w', Z w')) ⟨0, hn⟩ α w *
          (μ[fun w' => ∏ e, (edgeVar (θ w') e) ^ (β e - α e) |
            MeasurableSpace.comap (fun w' => rfun (θ w', Z w')) inferInstance]) w := by sorry

end AMPLowDeg.RankOne
