-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a545_C0_value_stopped_nonnegative_endpoint_AEStronglyMeasurable
-- name    : AvramDividend.Classical.avram_ga_a545_C0_value_stopped_nonnegative_endpoint_AEStronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:09:18.959287+00:00
-- url     : https://prove2.me/theorems/08de67b6-8250-4114-8e5f-2dd07adeff7d
-- title:
--   Measurability of a positive-domain value function at a nonnegative random endpoint
-- statement:
--   A function continuous on strictly positive reserves is almost everywhere strongly measurable at a measurable endpoint known nonnegative almost surely, even when the function has no regularity on negative reserves or at zero.
-- source:
--   Measurable positive-half-line extension (a544) and almost everywhere equality on nonnegative endpoint

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a544_positive_C0_value_Borel_extension
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a545_C0_value_stopped_nonnegative_endpoint_AEStronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ)))
    (Z : Ω → ℝ) (hZm : Measurable Z)
    (hZ0 : ∀ᵐ ω ∂P, 0 ≤ Z ω) :
    AEStronglyMeasurable (fun ω => w (Z ω)) P := by sorry
