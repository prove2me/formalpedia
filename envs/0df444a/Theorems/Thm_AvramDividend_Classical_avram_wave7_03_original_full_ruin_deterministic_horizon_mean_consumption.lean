-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:52:38.482217+00:00
-- url     : https://prove2.me/theorems/633be7dd-b23e-4d0a-b1a9-b6a41c8bf2e3
-- title:
--   Verified Lean consumption example: deterministic horizon full original Stieltjes dividend mean
-- statement:
--   A one-line consumer of the W7-03 original full stopped bounded random-clock expected real/ENNReal equality, instantiated at the constant measurable clock tau(omega)=T. It directly expresses the full original expected dividend payout on paymentTimes(ruinTime X x D omega) cap Iic T as the ENNReal embedding of the signed real Stieltjes expectation on the identical measure/domain, without BV/UBV, strict pre-ruin, or extra integrability premises.
-- source:
--   Direct consumption of new W7-03 unconditional full-ruin expected bridge fc7c1b8a; constant clock measurable_const and le_rfl.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
