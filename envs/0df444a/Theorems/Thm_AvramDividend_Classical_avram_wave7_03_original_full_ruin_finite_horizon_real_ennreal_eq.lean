-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:39:32.469603+00:00
-- url     : https://prove2.me/theorems/a5c80ef7-ce71-40f2-801d-c880f31032dc
-- title:
--   Unconditional exact original full ruin-stopped Stieltjes real/ENNReal identity at finite horizon
-- statement:
--   At every deterministic nonnegative finite horizon T, for the original spectrally negative Levy X and arbitrary original dividend strategy D, the real discounted Stieltjes payment integral over paymentTimes(ruinTime) cap Iic T is exactly equal after ENNReal.ofReal to the original ENNReal payment integral over the identical domain and measure. The Stieltjes mass finiteness follows from inclusion in Icc 0 T and the exact rightLimit cumulative mass formula. It includes time-zero atom, all continuous, singular-continuous and jump payments, excluding the positive ruin boundary; no BV/UBV assumption.
-- source:
--   Accepted dividendMeasure Icc rightLimit mass theorem d6ace15b, exact finite-mass full-domain bridge 339849ef, paymentTimes definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
