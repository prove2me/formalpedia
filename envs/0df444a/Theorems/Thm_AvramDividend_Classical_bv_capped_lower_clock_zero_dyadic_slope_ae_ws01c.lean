-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_capped_lower_clock_zero_dyadic_slope_ae_ws01c
-- name    : AvramDividend.Classical.bv_capped_lower_clock_zero_dyadic_slope_ae_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:00:09.969381+00:00
-- url     : https://prove2.me/theorems/83413997-64b7-4efd-9472-0e0d77962039
-- title:
--   The capped strict lower exit has an almost-sure zero dyadic residual slope
-- statement:
--   At each deterministic finite cap of the actual strict lower clock, the future Lévy path has the same full sample-path law as the original process. The countable Borel zero-dyadic-deficit event holds almost surely for the original path and is transferred through that exact path-law equality to the shifted path. This proves the process-specific random-clock zero-slope property.
-- source:
--   Exact original stochastic capped lower-clock zero-dyadic-slope statement, with the generic equal-law measurable-event transfer expanded inline from the complete work/avram_ws01c_equal_law_ae_borel_event_draft.lean so no ambiguous authoring job is imported. Full 68-line conditional proof work/avram_ws01c_capped_zero_slope_inline_event_solution_20261028.lean. Do NOT POST before genuine actual capped lower clock future-path sameLaw and origin zero deficit path cylinder prerequisites are canonically Proved; public exact-name search was zero at last check.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_capped_raw_lower_clock_NNReal_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_bv_actual_capped_lower_clock_future_path_sameLaw_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_dyadic_zero_slope_path_event_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_capped_lower_clock_zero_dyadic_slope_ae_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation)
    (lower : ℝ) (T : ℝ≥0)
    (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ) -
          (X.X
            ((twoSidedExitDownTime X lower ω ⊓
              (T : ℝ≥0∞)).toNNReal + ((1 : ℝ≥0) / 2) ^ n) ω -
           X.X
            ((twoSidedExitDownTime X lower ω ⊓
              (T : ℝ≥0∞)).toNNReal) ω)) /
          ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by sorry
