-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_full_source_increment_decomposition
-- name    : AvramDividend.Classical.avram_p3_bv_finite_cap_full_source_increment_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:03:57.795023+00:00
-- url     : https://prove2.me/theorems/16088056-93fc-48ab-9763-87c585139d03
-- title:
--   Exact linearly extended finite-cap candidate increment across arbitrary frozen source steps
-- statement:
--   For the original candidate extended linearly with unit slope above a finite dividend cap, each frozen-source increment equals the original candidate's increment between the clipped endpoints plus the exact signed cap-overshoot increment. This holds even when the physical source-frozen cell rises above the cap and therefore requires no unjustified frozen cap-bound assumption.
-- source:
--   Algebraic splitting of the same finite-cap spliced function used in the original P3-F stopped bounded-variation mesh. Direct equality, no added stochastic hypothesis.

import Mathlib

open scoped ENNReal

theorem AvramDividend.Classical.avram_p3_bv_finite_cap_full_source_increment_decomposition
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤) (w V : ℝ → ℝ)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ) :
    V (z + d) - V z =
      (w (min (z + d) C.toReal) - w (min z C.toReal)) +
        (max (z + d - C.toReal) 0 - max (z - C.toReal) 0) := by sorry
