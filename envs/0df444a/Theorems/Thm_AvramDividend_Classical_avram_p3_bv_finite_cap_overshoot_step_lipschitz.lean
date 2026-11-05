-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_overshoot_step_lipschitz
-- name    : AvramDividend.Classical.avram_p3_bv_finite_cap_overshoot_step_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:15:28.335904+00:00
-- url     : https://prove2.me/theorems/eb3d3c8c-0a80-4245-a78e-c635d1ecf0af
-- title:
--   Finite-cap overshoot correction is 1-Lipschitz across all real frozen-source steps
-- statement:
--   For every original physical-grid frozen reserve z, arbitrary real source increment d and finite cap c, the positive overshoot correction in the exact capped candidate identity has absolute increment at most the magnitude of d. This remains valid when the source step crosses the cap in either direction and provides an honest candidate Stieltjes/physical-mesh envelope without inventing cap bounds.
-- source:
--   Real-order case analysis of the cap overshoot in Proved finite-cap full source increment 16088056-93fc-48ab-9763-87c585139d03.

import Mathlib

theorem AvramDividend.Classical.avram_p3_bv_finite_cap_overshoot_step_lipschitz
    (c z d : ℝ) :
    |max (z + d - c) 0 - max (z - c) 0| ≤ |d| := by sorry
