-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable
-- name    : AvramDividend.Classical.avram_wave7_07_original_predictable_time_exponential_discount_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:40:00.669542+00:00
-- url     : https://prove2.me/theorems/6ab9dfd1-17cb-488f-b165-efbc01a6d0fa
-- title:
--   Exponential discount is measurable on original right-continuous predictable time-state sigma algebra
-- statement:
--   For any original nonnegative-time filtration, its right-continuous predictable sigma-algebra contains all deterministic time-halfline cylinders; hence the original-clock map (t,ω) ↦ exp(-q t) is predictable-measurable for any real q. The theorem removes the explicit discount-measurability assumption from W7-07's discounted original source generator bridge.
-- source:
--   W7-07 original predictable time-discount measurability using the exact Mathlib predictable Ioi × univ cylinder theorem and Borel generator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_predictable_time_exponential_discount_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (q : ℝ) :
    Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) := by sorry
