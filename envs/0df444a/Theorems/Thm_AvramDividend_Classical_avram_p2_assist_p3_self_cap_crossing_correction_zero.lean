-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_self_cap_crossing_correction_zero
-- name    : AvramDividend.Classical.avram_p2_assist_p3_self_cap_crossing_correction_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:26:52.597739+00:00
-- url     : https://prove2.me/theorems/f269c394-504c-430f-b1bf-2d61e16c3fb1
-- title:
--   Physical BV cap-crossing correction vanishes when the verification function is its own cap extension
-- statement:
--   For the actual piecewise linear finite-cap value extension V, the cap-crossing correction appearing in the Proved P3-F original physical C1 source-grid theorem 5f66fa7e becomes exactly zero when the value function is consistently instantiated as V itself. This is the algebraic cancellation required for a source-faithful P3 stopped mesh construction, including the infinite-cap branch.
-- source:
--   Original P3-F theorem 5f66fa7e exact κ formula, and original finite/infinite cap-extension hypotheses. Direct case distinction and cancellation; no stochastic hypotheses are introduced.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_self_cap_crossing_correction_zero
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (p : ℝ) :
    (if C = ⊤ then 0
     else if p ≤ C.toReal then 0
     else V C.toReal + (p - C.toReal) - V p) = 0 := by sorry
