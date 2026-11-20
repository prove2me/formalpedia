-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_scalar_finitecap_mesh_overshoot_defect_nonvanishing
-- name    : AvramDividend.Classical.avram_jump6_B_scalar_finitecap_mesh_overshoot_defect_nonvanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:03:37.714529+00:00
-- url     : https://prove2.me/theorems/7bcc2e44-268f-425b-b255-9c3c48e548fa
-- title:
--   Finite cap physical prepayment overshoot sum can persist under mesh refinement
-- statement:
--   A deterministic algebraic counterexample to the unsupported inference that a prepayment overshoot defect vanishes merely because each mesh overshoot tends to zero. For C=1, w(y)=y below C and 2-y above C, the caplinear V(y)=y gives a positive total defect equal to 2 for every positive number of mesh intervals. This theorem does not assert a counterexample to the stochastic Levy assumptions; it proves that pointwise continuity alone cannot eliminate the explicit weighted original-grid correction.

import Mathlib
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_scalar_finitecap_mesh_overshoot_defect_nonvanishing
    (m : ℕ) (hm : 0 < m) :
    let a : ℝ := 1 / (m : ℝ)
    let w : ℝ → ℝ := fun y => if y ≤ 1 then y else 2 - y
    let V : ℝ → ℝ := id
    (m : ℝ) * (V (1 + a) - w (1 + a)) = 2 := by sorry
