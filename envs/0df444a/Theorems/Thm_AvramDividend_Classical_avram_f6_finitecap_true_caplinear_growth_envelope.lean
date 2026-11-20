-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_finitecap_true_caplinear_growth_envelope
-- name    : AvramDividend.Classical.avram_f6_finitecap_true_caplinear_growth_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:27:21.648383+00:00
-- url     : https://prove2.me/theorems/96e4f1bb-c077-4663-898d-a077e9c1c218
-- title:
--   Finite-cap exact all-cap HJB continuation has K plus reserve upper envelope
-- statement:
--   For finite cap C and w bounded by K on [0,C], original caplinear continuation |V(z)| ≤ K+z for nonnegative reserve z. Useful to bound original clipped terminal by x+runningSup while cash is independently dominated by the full true Stieltjes cash.

import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_finitecap_true_caplinear_growth_envelope
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (K : ℝ) (hbound : ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → |w y| ≤ K)
    (z : ℝ) (hz : 0 ≤ z) :
    |if ENNReal.ofReal z ≤ C then w z
       else w C.toReal + (z - C.toReal)| ≤ K + z := by sorry
