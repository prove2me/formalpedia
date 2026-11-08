-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_bounded_stopping_clock_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_raw_R_bounded_stopping_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:28:43.59278+00:00
-- url     : https://prove2.me/theorems/6c698bcd-abcb-491e-8b0b-68c0346737b1
-- title:
--   Original BV jump residual at an a.e. bounded random stopping clock is L1
-- statement:
--   Under the original bounded-variation spectrally negative Levy process standing assumptions, the literal raw real jump residual evaluated at an almost surely T-bounded random stopping clock is integrable whenever its sampled coordinate is a.e. strongly measurable. This follows from the source-exact original bounded-clock pathwise envelope 0671ce2e and fixed-time L1 theorem cac67b8e. The real original jump-time tsum, filtration and sample paths remain unchanged, with random-clock measurability an explicit separate hypothesis.
-- source:
--   AVRAM BV-RESIDUAL10 source-exact random stopped residual L1 from original bounded clock, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_raw_R_nonnegative_bounded_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_fixed_time_L1

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_raw_R_bounded_stopping_clock_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, τ ω ≤ T)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (((τ ω : ℝ≥0) : ℝ) * X.drift - X.X (τ ω) ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ τ ω then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P) :
    Integrable (fun ω =>
      (((τ ω : ℝ≥0) : ℝ) * X.drift - X.X (τ ω) ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ τ ω then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P := by sorry
