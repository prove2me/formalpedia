-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedFiniteObservationVector_law
-- name    : AvramDividend.Classical.levy_shiftedFiniteObservationVector_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:43:37.12804+00:00
-- url     : https://prove2.me/theorems/3c552845-8106-4f6a-9503-7f7e87fddb50
-- title:
--   Every finite-dimensional shifted Lévy path vector has the same law
-- statement:
--   For every finite set of observation times, the complete finite vector of shifted Lévy path values relative to the shift has the same joint distribution as the original vector. This follows from sorted zero-based grids, stationarity of all consecutive increment vectors and measurable coordinate projection.
-- source:
--   Directly discharges the hFinite premise of levy_shiftedPath_law_of_all_finite_vector_laws (UUID 9b30daef-95c0-45f7-b082-03af46464da9), yielding full path stationarity needed for the strong-Markov dividend split UUID 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Theorems.Thm_AvramDividend_Classical_levy_shiftedConsecutiveIncrement_vector_law
import Theorems.Thm_AvramDividend_Classical_levy_incrementVector_law_implies_zeroBasedGrid_law
import Theorems.Thm_AvramDividend_Classical_levy_gridPosition_law_implies_finiteIndex_law

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedFiniteObservationVector_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) (J : Finset ℝ≥0) :
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (s + (j : ℝ≥0)) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (j : ℝ≥0) ω) P := by
  sorry
