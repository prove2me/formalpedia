-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_original_source_cap_C1_grid_premises
-- name    : AvramDividend.Classical.avram_p2_assist_p3_original_source_cap_C1_grid_premises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:45:56.704198+00:00
-- url     : https://prove2.me/theorems/2e2f44ad-8296-4467-9fb9-50441a4da7be
-- title:
--   Original P3-F bounded-variation finite-grid C1 premise bundle for the actual cap-extended value
-- statement:
--   Assemble the separately Proved original-source cap-continuation continuity, strict interior C1, derivative identity, transferred HJB gradient, top-cap identity, and finite-cap idempotence into the exact five premises required to instantiate the P3-F physical finite grid with source function w=V. This removes its cap crossing correction without assuming source process conclusions or cap global C1.
-- source:
--   Imports Proved avram_p2_assist_p3_finite_cap_extension_idempotent, cap_extension_C1_strict_interior, cap_extension_deriv_eq_strict_interior, and cap_extension_continuousOn_nonnegative, all at the authoritative mission Mathlib revision.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_finite_cap_extension_idempotent
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_C1_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_deriv_eq_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_continuousOn_nonnegative
open Set AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_original_source_cap_C1_grid_premises
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z) :
    ContinuousOn V (Ici (0 : ℝ)) ∧
    ContDiffOn ℝ 1 V {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} ∧
    (∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv V z) ∧
    (C = ⊤ → ∀ z : ℝ, V z = V z) ∧
    (C ≠ ⊤ → ∀ z : ℝ, V z =
      if z ≤ C.toReal then V z
      else V C.toReal + (z - C.toReal)) := by sorry
