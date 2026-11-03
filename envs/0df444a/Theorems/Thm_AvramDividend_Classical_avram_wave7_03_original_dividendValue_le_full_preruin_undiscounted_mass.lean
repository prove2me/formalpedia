-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_le_full_preruin_undiscounted_mass
-- name    : AvramDividend.Classical.avram_wave7_03_original_dividendValue_le_full_preruin_undiscounted_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:12:50.806294+00:00
-- url     : https://prove2.me/theorems/bde8eb86-8d85-462b-b60e-407ed8d7095f
-- title:
--   Actual original expected full discounted dividend cash bounded by pre-ruin undiscounted Stieltjes mass
-- statement:
--   For the canonical spectrally negative Levy source, genuine dividend strategy function D, ruinTime, paymentTimes and dividendMeasure, the original complete double-ENNReal expected discounted cash for q≥0 is bounded by the expected undiscounted mass of the identical full payment set on the actual P. No integrability, finiteness, or surrogate distribution is assumed. This bound includes the time-zero atom and all continuous and jump payments strictly preceding positive ruin, and enables finite-mass domination for BV and UBV verification consumers.
-- source:
--   Proved original paymentTimes_measurable 88dafb7f and general discounted_stieltjes_lintegral_le_measure fc69051f; source exact dividendValue definition and monotonicity outer lintegral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_dividendValue_le_full_preruin_undiscounted_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q) :
    dividendValue X q x D ≤
      (∫⁻ ω : Ω,
        (dividendMeasure D ω) (paymentTimes (ruinTime X x D ω)) ∂P) := by sorry
