-- Prove2me | Theorems.Thm_AvramDividend_Classical_ennreal_monotone_right_continuous_stieltjes
-- name    : AvramDividend.Classical.ennreal_monotone_right_continuous_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:13:29.135287+00:00
-- url     : https://prove2.me/theorems/3d932cfd-5bb9-47a7-8882-1a2fbfe2daa4
-- title:
--   Bounded ENNReal distribution has a real Stieltjes function
-- statement:
--   A monotone right-continuous ENNReal distribution bounded by one defines a real Stieltjes function by toReal. The resulting Stieltjes measure represents a possibly defective distribution.
-- source:
--   Use pinned ENNReal.toReal_mono, the accepted bounded toReal right-continuity theorem and StieltjesFunction constructor. Needed to construct the infinite-horizon Esscher survival distribution measure.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_ennreal_bounded_right_continuity_toReal
open MeasureTheory Set Topology
open scoped ENNReal

theorem AvramDividend.Classical.ennreal_monotone_right_continuous_stieltjes (F : ℝ → ℝ≥0∞) (hmono : Monotone F) (hright : ∀ x : ℝ, ContinuousWithinAt F (Ici x) x) (hbound : ∀ x : ℝ, F x ≤ 1) : ∃ S : StieltjesFunction ℝ, ∀ x : ℝ, S x = (F x).toReal := by sorry
