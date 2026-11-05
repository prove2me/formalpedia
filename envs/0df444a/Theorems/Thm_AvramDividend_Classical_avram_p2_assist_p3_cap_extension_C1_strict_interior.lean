-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_C1_strict_interior
-- name    : AvramDividend.Classical.avram_p2_assist_p3_cap_extension_C1_strict_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:33:10.856554+00:00
-- url     : https://prove2.me/theorems/58da7337-98cd-4a5e-8530-99eabaa902bc
-- title:
--   Actual finite or infinite cap-extended verification value inherits C1 regularity on the strict cap interior
-- statement:
--   The piecewise cap-linear extension V of the original candidate w agrees with w at every strict positive-cap interior point. Consequently its exact C1 regularity on the HJB interior follows from that of w. This is needed to instantiate the proved original P3-F source C1 grid with w=V and discharge its cap crossing correction using the separately Proved idempotence helpers.
-- source:
--   Mathlib ContDiffOn.congr, ENNReal.toReal_lt_toReal and ENNReal.toReal_ofReal, applied to the source-exact cap extension. No global smoothness at the cap is claimed.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_cap_extension_C1_strict_interior
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C}) :
    ContDiffOn ℝ 1 V
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by sorry
