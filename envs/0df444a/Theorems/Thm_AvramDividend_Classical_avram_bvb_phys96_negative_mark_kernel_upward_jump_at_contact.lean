-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys96_negative_mark_kernel_upward_jump_at_contact
-- name    : AvramDividend.Classical.avram_bvb_phys96_negative_mark_kernel_upward_jump_at_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:20:46.196882+00:00
-- url     : https://prove2.me/theorems/fec73ea5-58fa-4dd2-bf05-9461928becad
-- title:
--   Negative-mark jump kernel has an upward contact discontinuity
-- statement:
--   For a classical dividend candidate with w(0)>0 and a fixed negative jump of size one, the jump-reward kernel jumps upwards when positive pre-reserve reaches the jump size. This is the atom/contact obstruction to point-sampled quadrature in phys95.
-- source:
--   Original bounded-variation root branch phys95 mathematical validity analysis

import Mathlib
open Set

theorem AvramDividend.Classical.avram_bvb_phys96_negative_mark_kernel_upward_jump_at_contact (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 + y; w ((1 - ε) + (-1)) - w (1 - ε) < w (1 + (-1)) - w 1 := by sorry
