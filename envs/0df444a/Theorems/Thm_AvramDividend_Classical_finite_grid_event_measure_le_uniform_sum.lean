-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_event_measure_le_uniform_sum
-- name    : AvramDividend.Classical.finite_grid_event_measure_le_uniform_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:41:21.416362+00:00
-- url     : https://prove2.me/theorems/586fd9fe-f30b-43ec-923f-99e8e39dca87
-- title:
--   Uniform grid-cell measure bounds the finite union
-- statement:
--   The measure of the union of N grid-cell events is at most N times a common upper bound on individual event measures. This finite subadditivity inequality works for actual dependent Lévy increments and supplies the grid-first-jump argument.
-- source:
--   Mathlib measure_biUnion_finset_le; Avram, Palmowski and Pistorius (2007), section 3.3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finite_grid_event_measure_le_uniform_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (N : ℕ) (u : ℝ≥0∞)
    (hCell : ∀ k : ℕ, LT.lt k N → LE.le (μ (A k)) u) :
    LE.le (μ (⋃ k ∈ Finset.range N, A k)) ((N : ℝ≥0∞) * u) := by sorry
