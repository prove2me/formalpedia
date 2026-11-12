-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite73_excess_mono_of_deriv
-- name    : AvramDividend.Classical.avram_gfinite73_excess_mono_of_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:34:17.363844+00:00
-- url     : https://prove2.me/theorems/8bd3a1f9-fb93-4ce9-8c32-943eb8aef5e8
-- title:
--   Monotonicity of the cap excess value from the derivative bound
-- statement:
--   For a real value function continuous on a closed cap interval and differentiable in its interior, the lower bound w'≥1 implies that w(y)-y is nondecreasing. This is the analytic step needed to turn the Gaussian finite-cap gradient hypothesis into nonnegative cap-corner slack.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_gfinite73_excess_mono_of_deriv
    (w : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : ∀ z ∈ Ioo a b, DifferentiableAt ℝ w z)
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    MonotoneOn (fun z : ℝ => w z - z) (Icc a b) := by
  sorry
