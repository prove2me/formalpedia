-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_clipped_clock_zero_atom_lower_cutoff_lintegral_iSup
-- name    : AvramDividend.Classical.avram_wave7_19_original_clipped_clock_zero_atom_lower_cutoff_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:12:20.595203+00:00
-- url     : https://prove2.me/theorems/e37ed2bb-b657-49bd-93f6-f63db13851c9
-- title:
--   Original ruin cash is the zero right-payment atom plus increasing lower cutoffs at any strictly later finite stopping clock
-- statement:
--   For the original ruinTime, right-payment eligibility and full Stieltjes dividendMeasure, a deterministic integer clock strictly beyond the finite horizon leaves every positive-time lower-cutoff payment domain unchanged. The full discounted original finite-horizon cash is exactly the initial singleton right-dividend integral plus the increasing supremum of clipped-clock lower-cutoff Stieltjes integrals. It retains the zero right atom, handles overshoot or instant ruin without continuity, and makes the time and reserve stopping convention explicit for local Ito estimates.
-- source:
--   Accepted W7-19 exact strict clock stabilisation 62753faa-b3c6-4a84-ab5d-7379f6fceb89 and exact original zero atom monotone integral limit 818a0161-6937-4a3f-bee3-763a03c3bb48; W7-08 positive-horizon core 6004b387-9caa-4ee7-b466-2bf22d148505

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_finite_horizon_clock_strict_stabilises
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_cash_zero_atom_lower_cutoff_lintegral_iSup
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_clipped_clock_zero_atom_lower_cutoff_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (n : ℕ) (hn : ENNReal.ofReal T < (n : ℝ≥0∞)) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      ⨆ k : ℕ, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
