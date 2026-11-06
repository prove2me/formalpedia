-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_ruin_endpoint_cash_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_original_positive_ruin_endpoint_cash_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:46:23.9912+00:00
-- url     : https://prove2.me/theorems/2ffd301e-6b86-415b-a261-ec4e59e6e0ee
-- title:
--   Actual original positive ruin endpoint carries no admissible stopped dividend cash
-- statement:
--   At a strictly positive finite original ruin time tau, the stopped paymentTimes mask excludes its endpoint exactly. Hence the weighted original dividendMeasure integral over the ruin singleton is zero, without assuming that D itself has no jump at ruin. This discharges the endpoint-atom part of the GRID4 contact-tail continuity obligation.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_positive_ruin_endpoint_cash_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (τ : ℝ≥0)
    (hτ : 0 < τ)
    (hruin : (τ : ℝ≥0∞) = ruinTime X x D ω)
    (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ ({(τ : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by sorry
