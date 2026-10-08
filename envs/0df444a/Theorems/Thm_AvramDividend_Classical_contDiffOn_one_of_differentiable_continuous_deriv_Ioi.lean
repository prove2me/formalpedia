-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_differentiable_continuous_deriv_Ioi
-- name    : AvramDividend.Classical.contDiffOn_one_of_differentiable_continuous_deriv_Ioi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T17:40:45.936526+00:00
-- url     : https://prove2.me/theorems/0945dae7-0db3-4df6-8dc6-841872ed9e4d
-- title:
--   C1 regularity on the positive half-line from differentiability and continuous derivative
-- statement:
--   On the open positive half-line, if W is differentiable and its ordinary derivative is continuous, then W is C1 there. This isolates the final purely-calculus upgrade needed after an excursion or renewal representation establishes the derivative and its continuity.
-- source:
--   Pinned Mathlib contDiffOn_one_iff_derivWithin, uniqueDiffOn_Ioi and derivWithin_of_isOpen.

import Mathlib
open Set

theorem AvramDividend.Classical.contDiffOn_one_of_differentiable_continuous_deriv_Ioi
    (W : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ W (Ioi 0))
    (hcont : ContinuousOn (deriv W) (Ioi 0)) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
