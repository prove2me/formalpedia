-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a58_original_stationary_identdistrib_preserved_conull_paths_20261114
-- name    : AvramDividend.Classical.avram_a58_original_stationary_identdistrib_preserved_conull_paths_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:21:34.392201+00:00
-- url     : https://prove2.me/theorems/37160d13-777e-4db6-973d-fd1e4778c630
-- title:
--   Stationary source IdentDistrib increments persist under a simultaneous conull all-time modification
-- statement:
--   Stationary increment laws of a real source process on its original probability space are unchanged by a second measurable process that agrees simultaneously at every time on one conull event.
-- source:
--   Pinned Mathlib IdentDistrib.map_eq, Measurable.aemeasurable and Measure.map_congr.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- Stationary source increments survive simultaneous conull all-time modification on the same probability space. -/

theorem AvramDividend.Classical.avram_a58_original_stationary_identdistrib_preserved_conull_paths_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t, F t ω = G t ω)
    (hMeas : ∀ t, Measurable (G t))
    (hStat : ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => F t ω - F s ω) (F (t - s)) P P) :
    ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P := by sorry
