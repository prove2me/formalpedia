-- Prove2me | Theorems.Thm_AvramDividend_Classical_curvature_piecewise_continuousOn_of_stationary_join
-- name    : AvramDividend.Classical.curvature_piecewise_continuousOn_of_stationary_join
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:41:37.361358+00:00
-- url     : https://prove2.me/theorems/eab5c689-1cf1-44e8-a906-33a1022b117f
-- title:
--   Continuous curvature pasting across a stationary dividend barrier
-- statement:
--   For any real function W, if its ordinary second derivative is continuous at every positive reserve and vanishes at a barrier c, the profile equal to W'' at x<=c and zero at x>c is continuous on positive reserves. The lemma isolates the exact second-order pasting step between the Gaussian scale-value branch and the affine dividend-value branch.
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2 smooth fit, elementary continuous pasting of W''(c*)=0.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.OrderClosed
open Set Topology

namespace AvramDividend.Classical
/-- The second-derivative profile pastes continuously to the affine zero-curvature branch. -/
theorem curvature_piecewise_continuousOn_of_stationary_join
    (W : ℝ → ℝ) (c : ℝ)
    (hcont : ContinuousOn (deriv (deriv W)) (Ioi (0 : ℝ)))
    (hflat : deriv (deriv W) c = 0) :
    ContinuousOn ((Iic c).piecewise (deriv (deriv W))
      (fun _ : ℝ => (0 : ℝ))) (Ioi (0 : ℝ)) := by
  sorry
end AvramDividend.Classical
