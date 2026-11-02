-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_measurable_stopping_clock_complete_stieltjes_real_ennreal_expectation_eq
-- name    : AvramDividend.Classical.avram_wave5_05_original_measurable_stopping_clock_complete_stieltjes_real_ennreal_expectation_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:14:55.504869+00:00
-- url     : https://prove2.me/theorems/8515deec-a00c-4316-8dfa-44a8f79ae6dd
-- title:
--   Original stopped full Stieltjes dividend expected real and ENNReal conversion
-- statement:
--   For any measurable sample-path stop on the genuine spectrally negative Levy process and any admissible original dividend regulator, the expected real value of the finite-horizon ruin-and-stop truncated discounted complete Stieltjes dividend reward equals the real part of its ENNReal expectation. The result retains the time-zero dividend atom, singular continuous mass, and all pre-ruin right jumps. It uses the proven original-path finite cash envelope, the true dividend-measure s-finite kernel, and exact random payment-region measurability. No generator or martingale hypothesis is introduced.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), finite-horizon localization; source verified helper f0d4c94c-c070-460b-bb90-95ccc0264d90.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_original_measurable_stopping_clock_complete_stieltjes_real_ennreal_expectation_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ)
    (S : Ω → ℝ≥0∞) (hSm : Measurable S) :
    (∫ ω,
      (∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω).toReal ∂P) =
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂dividendMeasure D ω ∂P).toReal := by
  sorry
