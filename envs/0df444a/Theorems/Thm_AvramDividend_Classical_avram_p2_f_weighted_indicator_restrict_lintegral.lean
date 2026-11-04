-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_indicator_restrict_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_indicator_restrict_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:29:00.152341+00:00
-- url     : https://prove2.me/theorems/b237d92e-e674-45c4-ac52-480187205a33
-- title:
--   Exact indicator-weighted ENNReal count lintegral equals restricted lintegral
-- statement:
--   A genuine nonnegative random weight multiplied by a random count restricted to a measurable past event has exactly the corresponding restricted ambient lintegral. Holds without finiteness or even measurability of the factors, by indicator algebra and the pinned Mathlib indicator integral identity, including the 0*infinity case.
-- source:
--   Mathlib MeasureTheory.lintegral_indicator and Set.indicator pointwise; independent from original Levy intensity and canonical W7-06 targets.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_indicator_restrict_lintegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (H N : Ω → ℝ≥0∞) :
    (∫⁻ ω, H ω * A.indicator N ω ∂μ) =
    (∫⁻ ω in A, H ω * N ω ∂μ) := by sorry
