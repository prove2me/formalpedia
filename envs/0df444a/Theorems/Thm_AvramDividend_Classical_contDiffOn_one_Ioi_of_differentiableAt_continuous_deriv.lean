-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv
-- name    : AvramDividend.Classical.contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T15:20:15.860977+00:00
-- url     : https://prove2.me/theorems/9d3389ae-18cd-4720-8a8f-5e5f50941621
-- title:
--   C1 on the positive half-line from differentiability and continuous ordinary derivative
-- statement:
--   A real function that is differentiable at every positive point and has continuous ordinary derivative on (0,infinity) is continuously differentiable there. On the open half-line, derivWithin equals deriv, so this is an immediate application of Mathlib's characterisation contDiffOn_one_iff_derivWithin.
-- source:
--   Pinned Mathlib contDiffOn_one_iff_derivWithin, uniqueDiffOn_Ioi and derivWithin_of_isOpen.

import Mathlib
open Set

theorem AvramDividend.Classical.contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv
    (W : ℝ → ℝ)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (hcont : ContinuousOn (deriv W) (Ioi 0)) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
