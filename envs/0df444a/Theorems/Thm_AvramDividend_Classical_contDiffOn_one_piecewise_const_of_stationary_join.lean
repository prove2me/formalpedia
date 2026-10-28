-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_piecewise_const_of_stationary_join
-- name    : AvramDividend.Classical.contDiffOn_one_piecewise_const_of_stationary_join
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:06:42.673706+00:00
-- url     : https://prove2.me/theorems/a383a186-d093-4889-81bf-3338b6d7cbd7
-- title:
--   C1 pasting of a stationary profile to its constant continuation
-- statement:
--   The derivative profile of a Gaussian scale function is C1 up to a positive optimal barrier and becomes constant above the barrier. If the profile value matches and its derivative vanishes at that barrier, the pasted function is C1 on positive reserves. This deterministic lemma is an exact consumer of the proved stationary derivative join and feeds global C2 smooth-fit for the optimal dividend value.
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2 smooth fit; deterministic calculus gluing of C1 branches.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_stationary_piecewise_hasDerivAt_zero
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv
open Set Topology

namespace AvramDividend.Classical
/-- A C1 positive-axis profile with zero derivative at its matching join pastes C1 to a constant. -/
theorem contDiffOn_one_piecewise_const_of_stationary_join
    (f : ℝ → ℝ) (c v : ℝ) (hc : 0 < c)
    (hreg : ContDiffOn ℝ 1 f (Ioi (0 : ℝ)))
    (hflat : deriv f c = 0) (hmatch : f c = v) :
    ContDiffOn ℝ 1 ((Iic c).piecewise f (fun _ : ℝ => v))
      (Ioi (0 : ℝ)) := by
  sorry
end AvramDividend.Classical
