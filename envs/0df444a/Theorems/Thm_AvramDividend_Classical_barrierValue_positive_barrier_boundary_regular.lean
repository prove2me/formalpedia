-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_positive_barrier_boundary_regular
-- name    : AvramDividend.Classical.barrierValue_positive_barrier_boundary_regular
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:11:06.65986+00:00
-- url     : https://prove2.me/theorems/d16835fd-4443-4d0b-a4b4-d3d3be8bc553
-- title:
--   Continuity, nonnegative origin and zero negative extension of a positive-barrier value
-- statement:
--   For a positive barrier a, if W is continuous and nonnegative on the nonnegative half-line and W'(a)>0, then the formal barrier-value function is continuous on [0,infinity), has a nonnegative value at zero, and agrees with its prescribed zero extension on negative reserves. The lower branch is W(x)/W'(a), the upper branch is affine, and the two formulae agree at a.
-- source:
--   Elementary source-neutral calculus for the piecewise barrierValue definition in the Avram classical dividend formalisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set Topology
open scoped ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierValue_positive_barrier_boundary_regular
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hWcont : ContinuousOn W (Ici 0))
    (hWnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hder : 0 < deriv W a) :
    ContinuousOn (barrierValue W a) (Ici 0) ∧
      0 ≤ barrierValue W a 0 ∧
      ∀ y < 0, barrierValue W a y = 0 := by
  sorry

end AvramDividend.Classical
