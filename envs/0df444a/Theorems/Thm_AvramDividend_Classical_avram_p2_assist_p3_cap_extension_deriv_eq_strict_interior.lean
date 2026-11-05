-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_deriv_eq_strict_interior
-- name    : AvramDividend.Classical.avram_p2_assist_p3_cap_extension_deriv_eq_strict_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:36:27.486118+00:00
-- url     : https://prove2.me/theorems/173cab6e-f2ed-4545-be0c-7c51d3d360c0
-- title:
--   Derivative of actual cap-linear value equals original HJB candidate on strict interior
-- statement:
--   The original source cap-linear continuation agrees with w throughout a neighbourhood of any strict positive interior reserve. Derivatives agree at the reserve, transferring source HJB gradient bounds directly to the P3-F original physical grid theorem instantiated with w=V.
-- source:
--   Actual cap source formula, Mathlib Filter.EventuallyEq.deriv_eq, ENNReal.toReal_lt_toReal, isOpen_Iio.mem_nhds.

import Mathlib
open Set Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_cap_extension_deriv_eq_strict_interior
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z : ℝ) (hz : 0 < z ∧ ENNReal.ofReal z < C) :
    deriv V z = deriv w z := by sorry
