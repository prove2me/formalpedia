-- Prove2me | Theorems.Thm_CVPricing_Regret_ls_estimate_rate_normal
-- name    : CVPricing.Regret.ls_estimate_rate_normal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:38:17.48684+00:00
-- url     : https://prove2.me/theorems/b0f26923-b7c3-464d-b516-9436718dcbaf
-- title:
--   Eq. (11) — normal demand, linear link: E[‖â_t − a⁽⁰⁾‖²] = O(log t / t^α) under CVP
-- statement:
--   Consider the special case of normally distributed demand with a linear demand function: $h(x) = x$, $v \equiv 1$, and the noise $e_t$ is $N(0, \sigma^2)$-distributed and independent of $\mathcal F_{t-1}$. Let prices follow Controlled Variance Pricing with $\alpha > 1/2$ and deterministic initial prices. Then the least-squares estimate $\hat a_t$ of $a^{(0)}$ (which coincides with the MQLE in this case) satisfies
--
--   $$\mathbb E\big[\|\hat a_t - a^{(0)}\|^2\big] = O\Big(\frac{\log t}{t^\alpha}\Big), \tag{11}$$
--
--   i.e. there is $K > 0$ with $\mathbb E[\|\hat a_t - a^{(0)}\|^2] \le K \log t / t^\alpha$ for every $t \ge 2$.
--
--   In this case the conclusions of Proposition 3 follow from a self-contained argument, with no truncation at $T_{\rho_0}$.
--
--   **Formalization Note** $\hat a_t$ is `lsEstimateOf` from the referenced Keskin–Zeevi definitions, $P_t^{-1}$ times $(\sum d_i, \sum d_i p_i)$; $P_t$ is invertible for $t \ge 2$ because $p_1 \ne p_2$. The norm is Euclidean. The squared error is also asserted to be integrable.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 776 (PDF 8), eq. (11); proof pp. 781–782 (PDF 13–14)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP
import Definitions.Def_CVPricing_Regret_Process

open MeasureTheory ProbabilityTheory KeskinZeevi.SufficientConditions

namespace CVPricing.Regret

/-- Eq. (11) (den Boer–Zwart 2014, p. 776; proof pp. 781–782): for normally distributed demand with a
linear demand function (`h(x) = x`, `v ≡ 1`, noise `e_t ~ N(0, σ²)` independent of the past), under
CVP with `α > 1/2`, the least-squares estimate `â_t` (which equals the MQLE) satisfies
`E[‖â_t − a⁽⁰⁾‖²] = O(log t / t^α)`, for `t ≥ 2` with an explicit constant `K`. -/
theorem ls_estimate_rate_normal (M : Model) (hh : M.h = id) (hv : M.v = fun _ => 1)
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d)
    (hGauss : ∀ t : ℕ, 1 ≤ t →
      Indep (MeasurableSpace.comap (noise M p d t) inferInstance) (ℱ (t - 1)) P ∧
      P.map (noise M p d t) = gaussianReal 0 (M.σ ^ 2).toNNReal)
    (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
      Integrable (fun ω => euclidNorm
        (lsEstimateOf (fun s => p s ω) (fun s => d s ω) t - M.a0) ^ 2) P ∧
      ∫ ω, euclidNorm (lsEstimateOf (fun s => p s ω) (fun s => d s ω) t - M.a0) ^ 2 ∂P
        ≤ K * (Real.log t / (t : ℝ) ^ α) := by sorry

end CVPricing.Regret
