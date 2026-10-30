-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_genuine_Qp_pathwise_volume_ae_reward_transfer
-- name    : AvramDividend.Classical.avram_ws01h_genuine_Qp_pathwise_volume_ae_reward_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:02:58.176583+00:00
-- url     : https://prove2.me/theorems/660148a3-7ba2-401f-9dfe-8c4d2577bcb7
-- title:
--   Genuine Esscher Qp joint path-clock measure transfers any per-original-path Lebesgue-a.e. equality of measurable rewards
-- statement:
--   Under the actual original spectrally negative Lévy probability law and the genuine real Exp(p) independent observation clock reweighted by the path-dependent terminal Esscher density exp(θX_t−ψ(θ)t), any two jointly measurable nonnegative rewards that agree for Lebesgue-almost every observation time separately for each original sample path have exactly equal integrals under the genuine Qp. Prove directly by source actual likelihood joint measurability, twice applying Mathlib withDensity integration, and product Tonelli to compare each fixed-path exponential-clock fibre. This is the precise rigorous transfer needed to use the proved almost-everywhere shifted future rational/full survival equivalence after genuine capped stopping. No global Esscher path-space law, exit quotient, or stochastic identity is assumed.
-- source:
--   Proved source joint Lévy measurable d55462c3, true terminal Esscher density jointly measurable de339769, Mathlib lintegral_withDensity_eq_lintegral_mul and lintegral_prod; actual real exponential PDF withDensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_genuine_Qp_pathwise_volume_ae_reward_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (F G : Ω × ℝ → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G)
    (hFG : ∀ ω : Ω, ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      F (ω, r) = G (ω, r)) :
    (∫⁻ z : Ω × ℝ, F z ∂
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ z : Ω × ℝ, G z ∂
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) := by sorry
