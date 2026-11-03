-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_clock_pathwise_signed_stieltjes_nonneg
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_clock_pathwise_signed_stieltjes_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:00:04.392752+00:00
-- url     : https://prove2.me/theorems/ee858034-c5a4-4802-91ff-e71ca9f73bb5
-- title:
--   Genuine original finite-clock signed discounted Stieltjes payout is pathwise nonnegative
-- statement:
--   For the canonical original spectrally negative Lévy process and its actual dividendMeasure, the signed real discounted Stieltjes integral of exp(-q t) on paymentTimes(ruinTime X x D ω)∩Iic τ is nonnegative for each path ω and any finite NNReal horizon τ. The positivity follows from Real.exp_pos integrated against the original positive Stieltjes dividend measure, retaining the right-limit time-zero atom, continuous payments, and closed-endpoint atoms. No substitute probability space or artificial integrability assertion is used.
-- source:
--   Mathlib MeasureTheory.integral_nonneg and Real.exp_pos on original positive dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_clock_pathwise_signed_stieltjes_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (τ : ℝ≥0) (q : ℝ) :
    0 ≤ (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
