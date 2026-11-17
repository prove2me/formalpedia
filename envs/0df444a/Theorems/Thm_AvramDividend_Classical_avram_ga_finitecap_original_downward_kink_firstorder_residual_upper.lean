-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_finitecap_original_downward_kink_firstorder_residual_upper
-- name    : AvramDividend.Classical.avram_ga_finitecap_original_downward_kink_firstorder_residual_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:07:08.63396+00:00
-- url     : https://prove2.me/theorems/b9a6d6b8-ee53-4442-9e14-84b405a78a35
-- title:
--   Original finite-cap downward kink gives one-sided source first-order Taylor residual comparison
-- statement:
--   At the original rational finite-cap corner b<C, the slope α=deriv w b is at least one. For any two states and first-order coefficient g, the original affine-slope-one capped function V has a Taylor residual no greater than the slope-α smooth extension U. This expresses the favorable downward cap-kink sign without requiring its absolute local-time correction to converge to zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ga_finitecap_original_downward_kink_firstorder_residual_upper
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (j : ℕ) (g x y : ℝ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let α : ℝ := deriv w b
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    V y - V x - (if x ≤ b then g else 1) * (y - x) ≤
      U y - U x - (if x ≤ b then g else α) * (y - x) := by sorry
