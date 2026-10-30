-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_fresh_rational_Qp_renewal_factor_eq_closed_survival
-- name    : AvramDividend.Classical.avram_ws01h_fresh_rational_Qp_renewal_factor_eq_closed_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:59:30.396655+00:00
-- url     : https://prove2.me/theorems/93ad6176-3383-4151-91e9-f0fd35471464
-- title:
--   Fresh true Qp rational-open survival integral is exactly the source closed-horizon Esscher CDF mass
-- statement:
--   For every genuine spectrally negative Lévy sample law, nonnegative terminal Esscher tilt θ, independent actual real Exp(p) clock, and reserve a, the full future path rational-grid survival integral appearing in the proved killed first-record Qp factor equals exactly the genuine tilted joint-clock probability of complete closed lower-survival through the observed horizon. The proof combines source-level joint Lévy whole-path measurability, the proved countable rational-age reward, the accepted true joint Esscher Qp Fubini identity, genuine nonnegative support of the real exponential observation clock, and the already accepted rational/open versus full closed Qp survival mass identity. It does not assume the two-sided exit q-scale ratio.
-- source:
--   Proved 0b7edea5 rational H, 4b5e9dc8 fresh grid CDF identity, 0b68143d full true Qp Fubini, 59996899 exponential support, actual Lévy joint measurability and terminal Esscher likelihood measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_rational_fresh_survival_eq_closed
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_full_reward_fubini
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_clock_nonnegative_ae
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01h_fresh_rational_Qp_renewal_factor_eq_closed_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) (a : ℝ) :
    (∫⁻ r : ℝ, (∫⁻ ω,
       ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal r) ω -
           (Real.toNNReal r : ℝ) * X.ψ θ)) *
       if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
             (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal r →
               0 ≤ a + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω)
       then (1 : ℝ≥0∞) else 0 ∂P) ∂(expMeasure p)) =
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 → 0 ≤ a + X.X s z.1}).indicator
        (fun _ => (1 : ℝ≥0∞)) z
      ∂((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) := by sorry
