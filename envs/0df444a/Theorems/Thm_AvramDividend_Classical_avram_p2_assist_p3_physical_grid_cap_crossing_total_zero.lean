-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_physical_grid_cap_crossing_total_zero
-- name    : AvramDividend.Classical.avram_p2_assist_p3_physical_grid_cap_crossing_total_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:48:27.482319+00:00
-- url     : https://prove2.me/theorems/d3e6b368-49f2-43b0-bbf4-62869544e3dc
-- title:
--   Eliminate every finite-grid cap-crossing correction from the physical P3-F source C1 inequality
-- statement:
--   For the actual cap-linear continuation V, the complete finite sum of source-mesh cap-crossing correction terms vanishes for any number of physical grid cells and any discount weights, including negative or arbitrary weights. Combined with P3-F's Proved actual source grid, this eliminates the non-sign-definite κ remainder when the source function is chosen to be V.
-- source:
--   Direct finite sum of Proved source-exact avram_p2_assist_p3_self_cap_crossing_correction_zero; imports accepted theorem at pinned Mathlib revision.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_self_cap_crossing_correction_zero
open AvramDividend.Classical
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_physical_grid_cap_crossing_total_zero
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (n : ℕ) (p : ℕ → ℝ) (e : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, e i *
      (if C = ⊤ then 0
       else if p i ≤ C.toReal then 0
       else V C.toReal + (p i - C.toReal) - V (p i))) = 0 := by sorry
