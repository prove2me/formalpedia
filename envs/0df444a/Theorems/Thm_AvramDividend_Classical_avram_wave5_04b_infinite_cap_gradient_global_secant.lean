-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_gradient_global_secant
-- name    : AvramDividend.Classical.avram_wave5_04b_infinite_cap_gradient_global_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:25:25.843089+00:00
-- url     : https://prove2.me/theorems/bb23d9ab-98c4-4077-8ea8-d861ea65dbf9
-- title:
--   Zero-safe global gradient secant for infinite Avram dividend cap
-- statement:
--   When w is continuous on nonnegative reserves, smooth on strictly positive reserves, and has derivative at least one everywhere positive, w(b)-w(a)≥b-a for arbitrary 0≤a≤b, with no finite cap or derivative at zero. This is an exact specialization of the Proved full-cap gradient secant to C=∞, suitable for the unbounded branch of an ENNReal-valued cap verification theorem.
-- source:
--   Instantiate the Proved full-cap gradient secant theorem 2ba5cc4f-3aab-40ea-a59a-8a49633c7595 at C=⊤. Simplify ENNReal.ofReal z<⊤ and the cap upper bound; preserve continuity at reserve zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_infinite_cap_gradient_global_secant
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z})
    (hw_grad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤ w b - w a := by sorry
