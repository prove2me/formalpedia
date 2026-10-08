-- Prove2me | Theorems.Thm_CVPricing_Regret_cvp_regret_bound
-- name    : CVPricing.Regret.cvp_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:38:43.082593+00:00
-- url     : https://prove2.me/theorems/0f2d3266-ab15-4ccf-9946-1f4193fbea4d
-- title:
--   Theorem 1 — Regret(T, CVP) = O(T^α + T^(1−α) log T) for α > 1/2
-- statement:
--   Consider the single-product pricing model with mean demand $h(a_0^{(0)} + a_1^{(0)}p)$, variance $\sigma^2 v(\cdot)$ and noise satisfying (2), and let prices be set by Controlled Variance Pricing with parameters $\alpha \in (1/2, 1)$, $c$ in the policy's range and deterministic initial prices $p_1 \ne p_2$. Assume that the quasi-likelihood equations (3) have at most one root. Then
--
--   $$\operatorname{Regret}(T, \mathrm{CVP}) = O\big(T^\alpha + T^{1-\alpha}\log T\big),$$
--
--   that is, there is a constant $K > 0$, independent of $T$, with
--
--   $$\operatorname{Regret}(T) = \mathbb E\Big[\sum_{t=1}^T r(p_{\mathrm{opt}}, a^{(0)}) - r(p_t, a^{(0)})\Big] \le K\big(T^\alpha + T^{1-\alpha}\log T\big) \qquad \text{for all } T \ge 1.$$
--
--   The term $T^\alpha$ is the price of the enforced exploration (the taboo interval) and $T^{1-\alpha}\log T$ the price of estimation error. Choosing $\alpha = 1/2 + \delta$ gives regret $O(T^{1/2+\delta})$ for every $\delta > 0$.
--
--   **Formalization Note** The regret is nonnegative, so the bound needs no absolute value. $K$ may depend on the model, $\alpha$, $c$ and $p_1, p_2$. Disclosed hypotheses relative to the page: uniqueness of the root of (3) (the page notes roots need not be unique, and an adversarial choice among several roots can break the result), the strict inequality $a_0^{(0)} + a_1^{(0)}p_h > 0$ in the model, and a demand process described by its first two conditional moments and (2) rather than by a fixed distribution $D(p)$. The range of $c$ is the printed one.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 776 (PDF 8), Theorem 1; proof p. 782 (PDF 14)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP
import Definitions.Def_CVPricing_Regret_Process

open MeasureTheory

namespace CVPricing.Regret

/-- Theorem 1 (den Boer–Zwart 2014, p. 776): under Controlled Variance Pricing with `α > 1/2`,
`Regret(T, CVP) = O(T^α + T^{1−α} log T)`: there is `K > 0` (depending on the model, `α`, `c`
and the initial prices, but not on `T`) with `Regret(T) ≤ K (T^α + T^{1−α} log T)` for every
`T ≥ 1`. Initial prices are deterministic; the MQLE is assumed unique (disclosed). -/
theorem cvp_regret_bound (M : Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      regret M P p T ≤ K * ((T : ℝ) ^ α + (T : ℝ) ^ (1 - α) * Real.log T) := by sorry

end CVPricing.Regret
