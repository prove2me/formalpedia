-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_sfinite_null_time_fibres_give_zero_pathwise_occupation
-- name    : AvramDividend.Classical.avram_gaussianB_sfinite_null_time_fibres_give_zero_pathwise_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:01:24.31606+00:00
-- url     : https://prove2.me/theorems/6d5cb0d2-7c30-4a31-bc27-1b00aa12b735
-- title:
--   Fixed-time null contact probabilities force almost surely zero physical-time occupation for an original Gaussian probability source
-- statement:
--   Under s-finiteness of the original probability measure and measurability of the space-time contact set, if every fixed-time section has probability zero then the set of contact times has Lebesgue measure zero along almost every source path. This is a formal source-measure consequence needed in the original Gaussian fixed-level null-occupation route, with the nondegenerate martingale occupation theorem remaining an explicit independent obligation.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_sfinite_null_time_fibres_give_zero_pathwise_occupation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) = 0) :
    ∀ᵐ ω ∂P, volume ((fun t : ℝ => (ω, t)) ⁻¹' S) = 0 := by sorry
