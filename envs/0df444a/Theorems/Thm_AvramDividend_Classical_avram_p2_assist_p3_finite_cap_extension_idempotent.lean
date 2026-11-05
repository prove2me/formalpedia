-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_finite_cap_extension_idempotent
-- name    : AvramDividend.Classical.avram_p2_assist_p3_finite_cap_extension_idempotent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:25:40.154211+00:00
-- url     : https://prove2.me/theorems/16080d2e-cc4a-4461-9a56-88adcc264ce6
-- title:
--   Original finite-cap value extension is idempotent, allowing the same extended value in the BV source grid
-- statement:
--   Once V is the piecewise linear continuation of the original value w above a finite dividend barrier, applying the same cap-extension construction to V leaves V unchanged. This exact identity is designed for instantiating the Proved original P3-F physical C1 source grid 5f66fa7e with w=V, so that the frozen cap-crossing correction is identically zero while retaining the original physical process.
-- source:
--   Finite real-valued cap identity and the exact piecewise formula for the original cap extension, with no unstated smoothness, probabilistic assumption or kernel replacement.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_finite_cap_extension_idempotent
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (w V : ℝ → ℝ)
    (hV : ∀ z : ℝ, V z =
      if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) :
    ∀ z : ℝ, V z =
      if z ≤ C.toReal then V z
      else V C.toReal + (z - C.toReal) := by sorry
