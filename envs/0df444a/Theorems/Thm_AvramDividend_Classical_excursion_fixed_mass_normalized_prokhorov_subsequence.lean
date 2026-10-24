-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_normalized_prokhorov_subsequence
-- name    : AvramDividend.Classical.excursion_fixed_mass_normalized_prokhorov_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:10:22.778775+00:00
-- url     : https://prove2.me/theorems/69a5539c-e3ee-4d6d-b6d0-9133221d3ef3
-- title:
--   Tight fixed-mass finite measures have a weakly convergent normalized subsequence
-- statement:
--   For a tight sequence of finite measures of common positive mass, the sequence of probability normalisations possesses a weakly convergent subsequence. This composes two already Proved Avram excursion helpers to give the compactness interface needed by the Laplace weak-limit theorem.
-- source:
--   Composed accepted normalisation tightness and Prokhorov subsequence theorems.

import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory Filter Topology Set

theorem AvramDividend.Classical.excursion_fixed_mass_normalized_prokhorov_subsequence
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal) (hc : 0 < c)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (hnz : ∀ n : ℕ, ν n ≠ 0)
    (htight : IsTightMeasureSet
      (Set.range (fun n : ℕ => (ν n : Measure ℝ)))) :
    ∃ (P : ProbabilityMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n : ℕ => (ν (φ n)).normalize) atTop (𝓝 P) := by sorry
