-- Prove2me | Theorems.Thm_AvramDividend_Classical_sFinite_of_positive_lintegrable_density
-- name    : AvramDividend.Classical.sFinite_of_positive_lintegrable_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:33:00.38735+00:00
-- url     : https://prove2.me/theorems/6c8c6169-aced-470e-b7f6-169b5c289c60
-- title:
--   Positive integrable density implies s-finiteness of a measure
-- statement:
--   An a.e. measurable strictly positive density with finite lintegral makes the original measure SFinite. The weighted density measure is finite and the original measure is absolutely continuous with respect to it. Supports Fubini for Levy jump measures under the quadratic integrability condition.
-- source:
--   Pinned Mathlib WithDensity: isFiniteMeasure_withDensity, withDensity_absolutelyContinuous', Measure.sFinite_of_absolutelyContinuous.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem sFinite_of_positive_lintegrable_density
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞)
    (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, f x ≠ 0)
    (hint : ∫⁻ x, f x ∂μ ≠ ∞) :
    SFinite μ := by sorry

end AvramDividend.Classical
