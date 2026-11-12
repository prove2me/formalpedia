-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points
-- name    : AvramDividend.Classical.avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:40:33.114262+00:00
-- url     : https://prove2.me/theorems/eb289e43-b01b-4caa-af45-d51d687481ae
-- title:
--   Compact positive-volume contact set avoids every uniform-grid point
-- statement:
--   For every countable family of finite real grids, a compact positive-Lebesgue-volume subset of the unit interval misses every grid point. This gives the exact fat contact-set witness for the phys95 quadrature counterexample.
-- source:
--   Original BV phys95 counterexample witness from proven phys97 and phys99

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys97_compact_positive_mass_contact_avoids_null_grid
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys99_countable_uniform_grid_samples_are_null
open MeasureTheory Set

theorem AvramDividend.Classical.avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points (u : ℕ → ℕ → ℝ) : let G : Set ℝ := Set.range (fun p : ℕ × ℕ => u p.1 p.2); ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0 : ℝ) 1 ∧ Disjoint K G ∧ 0 < (volume : Measure ℝ) K := by sorry
