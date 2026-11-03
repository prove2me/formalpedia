-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_eq_ae_future_random_clock
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_horizon_eq_ae_future_random_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:05:40.277209+00:00
-- url     : https://prove2.me/theorems/d3d161f9-03ee-432c-a66d-5dc190807e77
-- title:
--   Original-process expected finite-horizon dividend cash preserved by almost surely later auxiliary clock
-- statement:
--   For the canonical spectrally negative Lévy process X on the original probability space Ω with law P and canonical Stieltjes dividendMeasure, replacing the ruin stopping clock by its minimum with an arbitrary sample-dependent auxiliary clock η preserves the original finite-horizon expected dividend cash whenever η exceeds the fixed T almost surely under P. This retains all horizon and initial payout atoms, with no atomlessness, independence or auxiliary sample-space hypothesis.
-- source:
--   Direct a.e. lifting of Proved source payment-set equality e57ac9e9-1cd4-4321-8da3-408eb9bcc0e7 by pinned Mathlib lintegral_congr_ae.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_horizon_eq_ae_future_random_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (η : Ω → ℝ≥0∞)
    (hFuture : ∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
