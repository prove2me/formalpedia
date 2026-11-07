-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
-- name    : AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:31:25.972897+00:00
-- url     : https://prove2.me/theorems/c7843154-ed4f-410e-a8de-067f46f30f50
-- title:
--   Canonical BV C1 finite-cap cutoff error is uniformly bounded by a scalar cap-corner secant defect
-- statement:
--   For finite positive dividend cap C and every interior cutoff b between zero and C, define the slope-one cap extensions V_C and V_b from an original BV C1 verification candidate w with derivative >=1 strictly below C. For every nonnegative reserve y including y>C, the difference V_C(y)-V_b(y) lies in [0,w(C)-w(b)-(C-b)]. This deterministic uniform estimate follows from two genuine closed-cap BV secants and needs no derivative of w at C. As b approaches C, the scalar bound tends to zero by continuity, resolving a finite-cap mesh error without unsupported smooth fit.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b y : ℝ) (hb0 : 0 ≤ b) (hbC : b ≤ C.toReal)
    (hy : 0 ≤ y) :
    0 ≤ (if y ≤ C.toReal then w y
         else w C.toReal + (y - C.toReal)) -
        (if y ≤ b then w y else w b + (y - b)) ∧
    (if y ≤ C.toReal then w y
     else w C.toReal + (y - C.toReal)) -
      (if y ≤ b then w y else w b + (y - b)) ≤
        (w C.toReal - w b) - (C.toReal - b) := by sorry
