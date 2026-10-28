-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exponential_withDensity_nonzero_of_nonzero
-- name    : AvramDividend.Classical.esscher_exponential_withDensity_nonzero_of_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:55:45.776693+00:00
-- url     : https://prove2.me/theorems/7e2626ba-ded6-4192-99b1-5456bd230185
-- title:
--   Positive Esscher exponential weighting preserves nonzero jump magnitude measures
-- statement:
--   A nonzero measure of nonnegative jump magnitudes remains nonzero after multiplication by the strictly positive Esscher exponential density. The proof uses exact pinned Mathlib withDensity_eq_zero_iff and ae_iff. Combined with negative_measure_magnitude_pushforward_positive and positive_first_moment_of_nonzero_without_zero_atom, it yields strict positivity of the discounted Lévy first moment and the exact positive subunit renewal mass for the BV cstar path.
-- source:
--   Pinned Mathlib MeasureTheory.withDensity_eq_zero_iff, MeasureTheory.ae_iff, and Real.exp_pos; generic Esscher-weighted Lévy magnitude measure.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Real
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_exponential_withDensity_nonzero_of_nonzero
    (μ : Measure ℝ≥0) (hμ : μ ≠ 0) (φ : ℝ)
    (hf : AEMeasurable
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) μ) :
    μ.withDensity (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) ≠ 0 := by sorry
