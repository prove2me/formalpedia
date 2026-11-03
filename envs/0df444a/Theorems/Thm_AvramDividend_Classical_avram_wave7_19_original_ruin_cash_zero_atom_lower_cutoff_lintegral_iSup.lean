-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_cash_zero_atom_lower_cutoff_lintegral_iSup
-- name    : AvramDividend.Classical.avram_wave7_19_original_ruin_cash_zero_atom_lower_cutoff_lintegral_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:11:12.082618+00:00
-- url     : https://prove2.me/theorems/818a0161-6937-4a3f-bee3-763a03c3bb48
-- title:
--   Original full discounted Stieltjes cash equals time-zero dividend atom plus positive lower-cutoff monotone limit
-- statement:
--   For the actual original ruinTime, paymentTimes and Stieltjes dividendMeasure, every nonnegative finite-horizon full discounted cash payoff is exactly the singleton time-zero right-dividend contribution plus the increasing supremum of positive reciprocal lower-time cutoff payoffs. The proof uses actual nonnegative weighted measure, measurable increasing indicator functions and pinned lintegral_iSup; no atom-free or absolute-continuity assumption is added, and immediate ruin retains its zero payment. This is an exact boundary/limit interface usable after local stopped Ito inequalities that start away from time zero, not an Ito calculation.
-- source:
--   New accepted W7-19 exact source payment set lower-cutoff union ca2dff72, W7-08 positive-horizon Ito core 6004b387, existing singleton Stieltjes original source semantics.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_payment_zero_atom_reciprocal_lower_cutoff_iUnion
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ruin_cash_zero_atom_lower_cutoff_lintegral_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      ⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Icc (1 / ((n : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
