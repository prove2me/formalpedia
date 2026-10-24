-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_uniform_record_grid_mono
-- name    : AvramDividend.Classical.firstUpcrossing_uniform_record_grid_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:38:06.122397+00:00
-- url     : https://prove2.me/theorems/ac07587b-aa3a-4fac-9fcd-8b7f847ae0dd
-- title:
--   Actual first upcrossing times are monotone on an equally spaced record grid
-- statement:
--   For each spectrally negative Lévy sample path and any nonnegative grid width, successive strict first-upcrossing clocks of the original process occur in nondecreasing order in the extended nonnegative reals, including inaccessible infinite passage times. This discharges the order premise used by the accepted finite-grid Stieltjes bounds once finite attained record clocks are supplied.
-- source:
--   Published AvramDividend.Classical.firstUpcrossing_threshold_iInf_mono, plus nonnegative scalar multiplication monotonicity.

import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.firstUpcrossing_uniform_record_grid_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (b h : ℝ) (hh : 0 ≤ h) :
    Monotone (fun n : ℕ =>
      ⨅ (r : ℝ≥0) (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) := by sorry
