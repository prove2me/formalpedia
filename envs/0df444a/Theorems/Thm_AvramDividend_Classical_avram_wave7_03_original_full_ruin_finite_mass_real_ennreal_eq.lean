-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:31:53.160655+00:00
-- url     : https://prove2.me/theorems/339849ef-34b7-4c4c-bc29-0181cf6f9319
-- title:
--   Exact full ruin-stopped same-measure real/ENNReal Stieltjes identity under finite mass
-- statement:
--   For the actual spectrally negative Levy X, original dividend strategy D and original Stieltjes dividendMeasure, the complete discounted payout through real horizon T on paymentTimes(ruinTime) cap Iic T equals the ENNReal embedding of the real integral over precisely the same set and measure, provided its mass is finite. Includes the time-zero right-limit atom, every interior jump and continuous payment, and excludes positive ruin-time boundary dividends. Both discount and domain are identical; no replacement process or alternate sample space.
-- source:
--   Accepted measurable paymentTimes 88dafb7f and generic exact finite-measure discounted Stieltjes payout bridge 72bc55bf; original dividendMeasure and ruinTime definitions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_finite_measure_payout_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T)
    (q : ℝ) (hq : 0 ≤ q)
    (hMass : (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ≠ ⊤) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
