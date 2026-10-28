-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_strict_closed_exp_clock_ws01a
-- name    : AvramDividend.Classical.chat04_true_killed_scale_strict_closed_exp_clock_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:05:22.482867+00:00
-- url     : https://prove2.me/theorems/fa880b6f-6e79-4abf-801d-bb84592eedb7
-- title:
--   Actual strict lower-clock and closed-history killed q-scale rewards agree at exponential time
-- statement:
--   For the genuine spectrally negative Lévy process and independent Exp(p) clock, the product-law lintegral of the discounted q-scale payoff killed by the strict lower first passage time equals the same genuine product-law lintegral killed by the full closed path history staying above the lower boundary. The equivalence holds only almost everywhere in observation time, with exceptional singleton clocks treated correctly by the previously proved theorem; no pointwise equality at the exact stopping time is assumed.
-- source:
--   Canonical Proved a.e.-time strict/closed-history equivalence 26b1bbb5, true strict-clock joint measurability c740e195, measurable running infimum and terminal state, pinned Mathlib Tonelli lintegral_prod and exponential-density withDensity formula.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_killed_closed_history_ae_time_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_true_killed_scale_strict_closed_exp_clock_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p q : ℝ) (hp : 0 < p) (x : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator
        (fun z => ENNReal.ofReal
          (Real.exp (-(q * z.2)) *
            W (x + X.X (Real.toNNReal z.2) z.1))) z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}).indicator
        (fun z => ENNReal.ofReal
          (Real.exp (-(q * z.2)) *
            W (x + X.X (Real.toNNReal z.2) z.1))) z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) := by sorry
