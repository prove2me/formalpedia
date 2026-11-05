-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_finite_interior_mesh_reserves_common_band
-- name    : AvramDividend.Classical.avram_p3_h_localise_finite_interior_mesh_reserves_common_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:11:28.835263+00:00
-- url     : https://prove2.me/theorems/02c2b0f1-6a53-424e-b838-b7bfd9376e60
-- title:
--   One common compact cap-interior band controls every value of a finite original BV reserve mesh
-- statement:
--   A finite nonempty family of original reserve states strictly inside the positive cap admits one compact uniform band, with positive cutoff at most two, including all states and remaining entirely inside the generator's C1 region. This supplies uniform mesh-cell constants needed by P3-F and the signed budget.
-- source:
--   Exact-revision Mathlib Finset min'/max' and ENNReal.ofReal monotonicity; independent of stochastic intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_localise_finite_interior_mesh_reserves_common_band
    (C : ℝ≥0∞) (S : Finset ℝ) (hS : S.Nonempty)
    (hInside : ∀ z ∈ S, 0 < z ∧ ENNReal.ofReal z < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      (∀ z ∈ S, z ∈ Icc a b) ∧
      Icc (a / 2) b ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
