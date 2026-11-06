-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_ruin_cofinal_local_cash_measurable
-- name    : AvramDividend.Classical.avram_sweep16_original_natural_ruin_cofinal_local_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:04:58.639994+00:00
-- url     : https://prove2.me/theorems/a056bf2c-31be-414d-830f-756d38a28310
-- title:
--   Original full-Stieltjes dividend cash is measurable at every genuine natural-ruin and cofinal stopping-time cutoff
-- statement:
--   For the unchanged physical spectrally negative Levy source X, original admissible D, natural finite ruin clock and any right-continuous-filtration stopping localizers S_k, each original closed-clock full-Stieltjes cash reward is measurable as a function of the same original sample omega. Derive measurability of ruinTime, S_k and the finite NNReal min clock, then invoke the Proved original random upper-clock full-Stieltjes cash measurability theorem, preserving all zero-time/right atoms. No additional sample space, source identity or uniform integrability assumption.
-- source:
--   Original cash and natural clock of SWEEP16 750ad13b and da912121 Fatou; Proved original ruinTime_measurable and random-upper-clock cash meas 2d478c7d.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_natural_ruin_cofinal_local_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k)) :
    ∀ k : ℕ, Measurable (fun ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
