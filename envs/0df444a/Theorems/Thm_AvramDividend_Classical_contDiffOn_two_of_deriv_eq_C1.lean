-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_two_of_deriv_eq_C1
-- name    : AvramDividend.Classical.contDiffOn_two_of_deriv_eq_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:20:14.367464+00:00
-- url     : https://prove2.me/theorems/c4b95b6d-7b3e-40d3-98a9-fe0101791146
-- title:
--   Transfer a C1 derivative to C2 regularity on the positive axis
-- statement:
--   If f is differentiable on the positive axis, its ordinary derivative agrees there with a C1 function g, then f is C2 there. This provides the final derivative-to-regularity transfer in the Gaussian scale-function Volterra argument.
-- source:
--   Mathlib contDiffOn_succ_iff_deriv_of_isOpen and the identification of derivatives on an open interval.

import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set

namespace AvramDividend.Classical

theorem contDiffOn_two_of_deriv_eq_C1
    (f g : ℝ → ℝ)
    (hfdiff : DifferentiableOn ℝ f (Ioi (0 : ℝ)))
    (hg : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hderiv : ∀ x : ℝ, 0 < x → deriv f x = g x) :
    ContDiffOn ℝ 2 f (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
