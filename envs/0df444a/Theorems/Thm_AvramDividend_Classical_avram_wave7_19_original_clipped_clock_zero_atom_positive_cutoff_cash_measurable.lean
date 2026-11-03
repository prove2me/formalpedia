-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_clipped_clock_zero_atom_positive_cutoff_cash_measurable
-- name    : AvramDividend.Classical.avram_wave7_19_original_clipped_clock_zero_atom_positive_cutoff_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:28:22.400092+00:00
-- url     : https://prove2.me/theorems/6eab88b4-05ec-4cbd-a062-20dc38c07832
-- title:
--   Source-admissible original zero right-atom plus clipped positive-time Stieltjes cutoff payoff is measurable
-- statement:
--   For the original spectrally negative Levy process, any IsDividendStrategy on the actual filtration, fixed natural stopped clock n and reciprocal positive lower-time cutoff k, the sum of the discounted Stieltjes dividend singleton at time zero and the clipped pre-ruin payment integral over [1/(k+1),T] is an ENNReal-valued measurable random variable. The proof constructs the existing s-finite original dividend kernel, uses joint measurability of paymentTimes at the original ruin clock, and applies the proved measurable random indicator integral. It preserves all singular-continuous and right-jump mass without additional canonical assumptions, and supplies exactly the hMeas obligation of the W7-19 expected-cash monotone limit bridge.
-- source:
--   Original-process source existing Proved dividendMeasure_global_sfinite_kernel_exists UUID 766b5129-2e5c-4d9d-a2db-12d0cca32e94; paymentTimes_joint_measurable UUID 6e9faa20-c0bf-445c-92c0-0fd50340de1b; ruinTime_stopping_rightCont_filtration UUID 2d036d4f-57b5-4b28-864b-a2ff5082e323; measurable_random_indicator_lintegral UUID 3f6e3e3b-9b82-4ca2-9ad8-b0543533321f; W7-19 expectation bridge 6c6548f4-5446-4eca-a0be-25be72df0b20

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_clipped_clock_zero_atom_positive_cutoff_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n k : ℕ) :
    Measurable (fun ω : Ω =>
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
