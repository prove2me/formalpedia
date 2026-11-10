-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite27_original_strict_stopped_rewards_global_meas
-- name    : AvramDividend.Classical.avram_gfinite27_original_strict_stopped_rewards_global_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T03:31:24.712919+00:00
-- url     : https://prove2.me/theorems/677a907e-05de-4b18-95d5-924d18aa90e8
-- title:
--   Original strict stopped dividend rewards are measurable at any cap
-- statement:
--   Necessary measurable-reward input to finite-cap Fatou passage 3308ae9d. For original dividends and any right-continuous-filtration NNReal stopping times, the strict cash plus terminal reward is measurable globally, including zero-clock, ruin, and payment-endpoint cases. Global measurability of w follows from continuity on nonnegative reserves and zero extension to negative reserves and requires no top-cap assumption.
-- source:
--   Adapt accepted Proved 2d275ef9 source word for word except use the already Proved cap-extension global w measurability theorem at synthetic cap top, avoiding a finite-cap split.

import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite27_original_strict_stopped_rewards_global_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (ρ : ℕ → Ω → ℝ≥0)
    (hρstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ j ω : WithTop ℝ≥0))) :
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
      if ζ ω = 0 then w x else
        Real.exp (-(q * (ζ ω : ℝ))) *
          w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    (∀ j, Measurable (H (ρ j))) ∧ AEStronglyMeasurable (H σ) P := by sorry
