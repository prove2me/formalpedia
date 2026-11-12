-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys97_compact_positive_mass_contact_avoids_null_grid
-- name    : AvramDividend.Classical.avram_bvb_phys97_compact_positive_mass_contact_avoids_null_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:27:54.338012+00:00
-- url     : https://prove2.me/theorems/75291932-d950-4228-ba5e-6d1a350d2f3e
-- title:
--   Compact positive-mass contact set can avoid null physical grids
-- statement:
--   Under finite positive mass and inner regularity, any measurable null family of deterministic sample points can be avoided by a compact positive-mass subset of the contact region. The physical grid can miss a positive-mass contact set.
-- source:
--   Original BV phys95 contact-set counterexample prerequisite

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_bvb_phys97_compact_positive_mass_contact_avoids_null_grid {α : Type*} [MeasurableSpace α] [TopologicalSpace α] (μ : Measure α) [μ.InnerRegularCompactLTTop] (A N : Set α) (hA : MeasurableSet A) (hN : MeasurableSet N) (hNzero : μ N = 0) (hAf : μ A ≠ ⊤) (hApos : 0 < μ A) : ∃ K : Set α, IsCompact K ∧ K ⊆ A ∧ Disjoint K N ∧ 0 < μ K := by sorry
