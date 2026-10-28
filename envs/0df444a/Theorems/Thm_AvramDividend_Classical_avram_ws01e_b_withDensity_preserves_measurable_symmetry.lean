-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_withDensity_preserves_measurable_symmetry
-- name    : AvramDividend.Classical.avram_ws01e_b_withDensity_preserves_measurable_symmetry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:43:23.699092+00:00
-- url     : https://prove2.me/theorems/d04f8b9f-41e4-42dd-8704-7418190a34fa
-- title:
--   Symmetry-preserving density tilts preserve exact event probabilities
-- statement:
--   For any measurable path transformation R preserving a base measure μ, and any nonnegative measurable density w invariant pointwise under R, the tilted measure μ.withDensity w gives equal probabilities to A and R inverse image A for any measurable event A. This is the generic exact symmetry-preserving change-of-measure lemma needed to transfer finite-grid Lévy increment reversal from the original law to an Esscher tilt, whose terminal likelihood depends on the total sum of increments and is invariant under reversing their order.
-- source:
--   Pinned Mathlib withDensity_apply, lintegral_indicator and lintegral_map, plus measurability and equality of the original pushforward law.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

/-- A density depending only on a symmetry-invariant statistic preserves
the base law's exact event symmetry under the same measurable map. -/

theorem AvramDividend.Classical.avram_ws01e_b_withDensity_preserves_measurable_symmetry
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (R : α → α) (hR : Measurable R)
    (hSym : Measure.map R μ = μ)
    (w : α → ℝ≥0∞) (hw : Measurable w)
    (hwR : ∀ x, w (R x) = w x)
    (A : Set α) (hA : MeasurableSet A) :
    (μ.withDensity w) (R ⁻¹' A) = (μ.withDensity w) A := by sorry
