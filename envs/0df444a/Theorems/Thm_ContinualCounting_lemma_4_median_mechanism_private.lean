-- Prove2me | Theorems.Thm_ContinualCounting_lemma_4_median_mechanism_private
-- name    : ContinualCounting.lemma_4_median_mechanism_private
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:02.467237+00:00
-- url     : https://prove2.me/theorems/6c7b7e27-8978-42ab-b22f-13b7da5bd4b0
-- title:
--   Lemma 4 — $\widehat M_s$ is private on inputs supported on $\mathcal L(\mathcal T^s)$
-- statement:
--   Let $h$ be even, $\varepsilon>0$, $\delta\ge0$, let $\nu$ be a probability law such that the oblivious mechanism $x\mapsto Ax+z$, $z\sim\nu$, is $(\varepsilon,\delta)$-DP, let $s\in\{\ell,r\}^{h/2}$, and let $\varphi_L,\varphi_R$ be measurable predictor families. Then for all neighbouring $x,x'\in\{0,1\}^{2^h}$ with $x_i=x'_i=0$ for $i\notin\mathcal L(\mathcal T^s)$ and every measurable set $S$ of outputs,
--   $$\Pr[\widehat M_s(x)\in S]\le e^{3\varepsilon}\Pr[\widehat M_s(x')\in S]+3\delta.$$
--
--   So the attack on $\widehat M_s$ contradicts the privacy of the original mechanism, on the inputs on which it is run.
--
--   Differences from the source:
--   - generalization: the predictors m^u_ℓ, m^u_r (measurable minimizers) → every measurable predictor family φL, φR; reason: the privacy argument never uses minimality; the paper's predictors are an instance
--   - generalization: §5 assumes n is a power of 16 and δ ∈ [0, 1) → every even h, and every δ ≥ 0; reason: the argument (composition, post-processing) uses neither restriction
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 4, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_ContinualCounting_oblivious
import Definitions.Def_ContinualCounting_medianMechanism

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Lemma 4 (`M̂_s` is private on inputs supported on `L(T^s)`).** Bairaktari, Dahl, Larsen,
arXiv:2607.00876 (sha256 986e6426…), p.24: "The mechanism M̂_s is (3ε, 3δ)-DP when restricted to inputs
x ∈ {0, 1}^n with x_i = 0 for i ∉ L(T^s)."

**Formalization Note.** Stated for every measurable predictor family, of which the paper's `m^u_ℓ, m^u_r`
are one; the privacy argument never uses the minimizer property. `ν` is the noise law of the
`(ε, δ)`-DP oblivious mechanism. `h` even is §5's standing assumption. -/
theorem lemma_4_median_mechanism_private {h : ℕ} (hh : Even h) (ν : Measure (Fin (2 ^ h) → ℝ))
    [IsProbabilityMeasure ν] (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ) (hDP : IsDP (oblivious ν) ε δ)
    (s : Fin (h / 2) → Bool) (φL : PredictorsL h) (φR : PredictorsR h)
    (hφL : ∀ u, Measurable (φL u)) (hφR : ∀ u, Measurable (φR u)) :
    IsApproxDP (RestrictedNeighbor h s) (medianMechanism ν s φL φR) (3 * ε) (3 * δ) := by sorry

end ContinualCounting
