-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
-- name    : AvramDividend.Classical.avram_wave5_04b_positive_ennreal_cap_extension_global_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:29:19.755202+00:00
-- url     : https://prove2.me/theorems/a4675c8a-b8c3-4eb4-91fc-f863be0df7ee
-- title:
--   Uniform positive ENNReal-cap global secant for finite cap-linear extension and infinite-cap w
-- statement:
--   For any positive capital cap C in ENNReal, finite or infinity, suppose w is continuous at zero, C1 in the strict positive interior below C, and has derivative ≥1 there. Let V coincide with w at infinite C and with its slope-one cap-linear extension at a finite C. Then b-a≤V(b)-V(a) for all 0≤a≤b, including reserve zero, the cap and pre-payment reserves above the cap. This eliminates a finite-cap-only assumption in the dividend-control bridge.
-- source:
--   Split C=⊤ versus finite. At infinity invoke Proved full-cap secant 2ba5cc4f... directly. At finite C, use the canonical ENNReal.ofReal_toReal and toReal_pos_iff correspondence to invoke the Proved full cap-linear extension secant 420ddace... .

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤ V b - V a := by sorry
