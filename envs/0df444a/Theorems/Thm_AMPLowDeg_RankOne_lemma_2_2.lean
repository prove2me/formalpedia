-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_2_2
-- name    : AMPLowDeg.RankOne.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:05:18.128598+00:00
-- url     : https://prove2.me/theorems/79b7d1ab-9913-4763-98be-0df548aa8d83
-- title:
--   Lemma 2.2 — conditional-cumulant lower bound (2.11)
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$ and $D\ge0$. On a probability space let $\theta$ (i.i.d. $\pi$) and the noise $W$ (i.i.d. $\mathcal N(0,1)$ on $\mathcal E_n$) be independent, and let $Z$ be external randomness independent of $(\theta,W)$. For every auxiliary observation $R=R(\theta,Z)\in\mathbb R^N$ with $R$ measurable, and $A_\alpha(\theta)=\mathbb E[\mathcal K_\alpha(R)\mid\theta]$ as in (2.10),
--
--   $$
--   \mathrm{MMSE}_{\le D}\ \ge\ m_2-\sum_{|\alpha|\le D}\frac{\mathbb E[A_\alpha(\theta)^2]}{n^{|\alpha|}\,\alpha!},
--   $$
--
--   the sum running over all $\alpha\in\mathbb N_0^{\mathcal E_n}$ with $|\alpha|\le D$, including $\alpha=0$.
--
--   This is the bound used in the rest of the proof: with the channel (2.9) its right-hand side is split into the tree part (Lemma 2.4), the vanishing part (Lemma 2.5(1)) and the non-tree part (Lemma 2.5(2)).
--
--   Differences from the source:
--
--   - reading: Z is external randomness → Z is a measurable random element of an arbitrary measurable space, and R = r(θ, Z) for a measurable r : (ℝⁿ × space of Z) → ℝ^N; reason: the source leaves the space of Z unspecified
--   - encoding: MMSE_{≤D} ≥ x with MMSE_{≤D} a real infimum → ENNReal.ofReal x ≤ mmseLD π n D, the risk being a lower Lebesgue integral in [0, ∞]; reason: MMSE_{≤D} is finite (the zero estimator has risk m₂), so for a finite value both forms say the same; no integrability convention is involved
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 8, Lemma 2.2, eq. (2.11); proof pp. 9–11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Graph
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma 2.2, p. 8 — conditional-cumulant lower bound (2.11): for every auxiliary observation
`R = R(θ, Z) ∈ ℝ^N`, where `Z` is independent of `(θ, W)`,
`MMSE_{≤D} ≥ m₂ − Σ_{|α| ≤ D} E[A_α(θ)²] / (n^{|α|} α!)`, with `A_α(θ) = E[𝒦_α(R) | θ]`. -/
theorem lemma_2_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0) (hmom : AllMomentsFinite π)
    (n N D : ℕ) (hn : 0 < n) {𝒵 : Type*} [MeasurableSpace 𝒵]
    (θ : Ω → Fin n → ℝ) (W : Ω → Edge n → ℝ) (Z : Ω → 𝒵)
    (hθ : Measurable θ) (hW : Measurable W) (hZ : Measurable Z)
    (hθlaw : μ.map θ = Measure.pi fun _ : Fin n => π)
    (hWlaw : μ.map W = Measure.pi fun _ : Edge n => gaussianReal 0 1)
    (hθW : IndepFun θ W μ) (hZind : IndepFun Z (fun w => (θ w, W w)) μ)
    (rfun : (Fin n → ℝ) × 𝒵 → Fin N → ℝ) (hr : Measurable rfun) :
    ENNReal.ofReal (m2 π - ∑ α ∈ multiIdx n D,
        (∫ w, (Acum μ θ (fun w' => rfun (θ w', Z w')) ⟨0, hn⟩ α w) ^ 2 ∂μ) /
          ((n : ℝ) ^ absIdx α * (factIdx α : ℝ))) ≤ mmseLD π n D := by sorry

end AMPLowDeg.RankOne
