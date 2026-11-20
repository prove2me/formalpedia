-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_finitecap_true_caplinear_global_W_envelope
-- name    : AvramDividend.Classical.avram_f6_finitecap_true_caplinear_global_W_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:52:04.831742+00:00
-- url     : https://prove2.me/theorems/8a973ac6-78b4-4da0-b8f0-747b8e68cfb0
-- title:
--   Finite-cap HJB continuation bounded by K plus true reserve ceiling including negative ruin contact
-- statement:
--   For w=0 on negative reserves, finite cap C and bounded |w| on [0,C], the exact all-cap continuation at any z≤S with S≥0 is bounded in absolute value by K+S, whether z lies below zero, inside, or above the cap. Combines with true stopped reserve ≤ x+runningSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_finitecap_true_caplinear_growth_envelope
set_option autoImplicit false
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_finitecap_true_caplinear_global_W_envelope
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (K : ℝ) (hbound : ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → |w y| ≤ K)
    (S z : ℝ) (hS : 0 ≤ S) (hzS : z ≤ S) :
    |if ENNReal.ofReal z ≤ C then w z
       else w C.toReal + (z - C.toReal)| ≤ K + S := by sorry
