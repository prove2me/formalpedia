-- Prove2me | Theorems.Thm_CVPricing_Regret_price_sq_error_rate
-- name    : CVPricing.Regret.price_sq_error_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:38:43.020623+00:00
-- url     : https://prove2.me/theorems/ef220b1d-0f3b-4a76-b8fe-c80fa8c40672
-- title:
--   Proof of Theorem 1, p. 782 — E[(p_t − p_opt)²] = O(t^(α−1) + log t / t^α)
-- statement:
--   Under the assumptions of Theorem 1 (the demand model, Controlled Variance Pricing with $\alpha > 1/2$, deterministic initial prices, a unique root of (3)), the expected squared pricing error satisfies
--
--   $$\mathbb E\big[(p_t - p_{\mathrm{opt}})^2\big] = O\Big(t^{\alpha - 1} + \frac{\log t}{t^\alpha}\Big),$$
--
--   i.e. there is $K > 0$ with $\mathbb E[(p_t - p_{\mathrm{opt}})^2] \le K(t^{\alpha-1} + \log t / t^\alpha)$ for every $t \ge 2$.
--
--   The term $t^{\alpha-1}$ is the squared length of the taboo interval and $\log t / t^\alpha$ is the estimation error; summing over $t$ and using (17) gives Theorem 1.
--
--   **Formalization Note** Stated for $t \ge 2$ because $\log 1 = 0$; the constant $K$ depends on the model, $\alpha$, $c$ and the initial prices, but not on $t$.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 782 (PDF 14), proof of Theorem 1, display after (20)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP
import Definitions.Def_CVPricing_Regret_Process

open MeasureTheory

namespace CVPricing.Regret

/-- Closing bound of the proof of Theorem 1 (den Boer–Zwart 2014, p. 782): under CVP with
`α > 1/2`, `E[(p_t − p_opt)²] = O(t^{α−1} + log t / t^α)`, stated for `t ≥ 2` with an explicit
constant `K`. -/
theorem price_sq_error_rate (M : Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
      ∫ ω, (p t ω - pOpt M) ^ 2 ∂P
        ≤ K * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) := by sorry

end CVPricing.Regret
