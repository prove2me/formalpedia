-- Prove2me | Theorems.Thm_ContinualCounting_lemma_5_median_noise_bound
-- name    : ContinualCounting.lemma_5_median_noise_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:43.43348+00:00
-- url     : https://prove2.me/theorems/81a5393c-9373-471e-a946-82aa8b4afa6e
-- title:
--   Lemma 5 — median-of-three noise is bounded by the squared prediction error
-- statement:
--   Let $h$ be even, let $\nu$ be a probability law of $z$, and let $u\in\mathcal T^s$ be at even depth $2d<h$. For measurable predictors $\varphi_L,\varphi_R$, if $s_{d+1}=r$,
--   $$\mathbb E\Big[\mathrm{median}_{k=1,2,3}\{b^{(k)}_{r(u)}-\varphi_L(\Delta^{<\ell(\ell(u))}(z^{(k)}),\Delta^{<\ell(r(u))}(z^{(k)}))\}^2\Big]\le3\,\mathbb E\big[|b_{r(u)}-\varphi_L(\Delta^{<\ell(\ell(u))}(z),\Delta^{<\ell(r(u))}(z))|\big]^2,$$
--   and if $s_{d+1}=\ell$,
--   $$\mathbb E\Big[\mathrm{median}_{k=1,2,3}\{b^{(k)}_{r(\ell(u))}-b^{(k)}_{r(u)}-b^{(k)}_{r(r(u))}-\varphi_R(\Delta^{<r(\ell(u))}(z^{(k)}),\Delta^{<r(r(u))}(z^{(k)}))\}^2\Big]\le3\,\mathbb E\big[|b_{r(\ell(u))}-b_{r(u)}-b_{r(r(u))}-\varphi_R(\Delta^{<r(\ell(u))}(z),\Delta^{<r(r(u))}(z))|\big]^2.$$
--   For the minimizers $\varphi_L=m^u_\ell$, $\varphi_R=m^u_r$ the right side is $3\sigma^2_{u,\tilde s_{d+1}}$, as the paper states.
--
--   The noise of $\widehat M_s$ in each coordinate is therefore controlled by the residual noise.
--
--   Differences from the source:
--   - generalization: m^u_ℓ, m^u_r, with right side 3σ²_{u,s̃_{d+1}} → every measurable predictor, with right side 3(E|prediction error|)²; reason: the minimizers supplied by `sigma_attained` have expected absolute error σ_{u,s̃_{d+1}}, which gives the printed bound
--   - generalization: §5 assumes n is a power of 16 → every even h; reason: the bound uses only that the three copies are i.i.d.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 5, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_ContinualCounting_medianMechanism

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Lemma 5 (median-of-three noise is bounded by the squared absolute prediction error).** Bairaktari,
Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), p.25: for `u ∈ T^s` at even depth `2d < h`,
`E[median_{k=1,2,3}{b^{(k)}_{r(u)} − m^u_ℓ(∆^{<ℓ(ℓ(u))}(z^{(k)}), ∆^{<ℓ(r(u))}(z^{(k)}))}²] ≤ 3 · σ²_{u,s̃_{d+1}}` if
`s_{d+1} = r`, and
`E[median_{k=1,2,3}{b^{(k)}_{r(ℓ(u))} − b^{(k)}_{r(u)} − b^{(k)}_{r(r(u))} − m^u_r(∆^{<r(ℓ(u))}(z^{(k)}), ∆^{<r(r(u))}(z^{(k)}))}²] ≤ 3 · σ²_{u,s̃_{d+1}}`
if `s_{d+1} = ℓ`.

**Formalization Note.** Stated for every measurable predictor family, with the expected absolute
prediction error in the bound; the paper's `m^u_ℓ, m^u_r` are the instances whose expected absolute error
is `σ_{u,s̃_{d+1}}`, and `sigma_attained` provides such a measurable predictor. The two cases are the two
values of `letter s d`; `predictionError` is the first expression if `s_{d+1} = r` and the second if
`s_{d+1} = ℓ`. -/
theorem lemma_5_median_noise_bound {h : ℕ} (hh : Even h) (ν : Measure (Fin (2 ^ h) → ℝ))
    [IsProbabilityMeasure ν] (s : Fin (h / 2) → Bool) (φL : PredictorsL h) (φR : PredictorsR h)
    (hφL : ∀ u, Measurable (φL u)) (hφR : ∀ u, Measurable (φR u)) (u : Node)
    (hu : u ∈ outputNodes h s) :
    ∫⁻ zz, ‖medianNoise φL φR (letter s (u.1 / 2)) u zz‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin 3 => ν) ≤
      3 * (∫⁻ z, ‖predictionError φL φR (letter s (u.1 / 2)) u z‖ₑ ∂ν) ^ 2 := by sorry

end ContinualCounting
