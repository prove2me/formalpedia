-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilt_origin_of_right_limit
-- name    : AvramDividend.Classical.esscher_tilt_origin_of_right_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:27:17.145228+00:00
-- url     : https://prove2.me/theorems/532ce6d5-0679-4314-a380-b1c56b6bbeb0
-- title:
--   Esscher-tilted right limit fixes the zero-boundary scale value
-- statement:
--   For any continuous-from-the-right real function W, if its Esscher exponential tilt tends to a finite constant r at zero, then W(0)=r. This deterministic bridge will turn the canonical geometric renewal measure's atom-at-zero asymptotics into the bounded-variation q-scale normalisation W(0)=1/d.
-- source:
--   Continuity of exponential tilt at the origin; used with Avram, Palmowski and Pistorius (2007), https://arxiv.org/pdf/math/0702893

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Instances.Real.Lemmas
open Filter

namespace AvramDividend.Classical

/-- A finite Esscher-tilted right boundary limit identifies the continuous scale value at zero. -/
theorem esscher_tilt_origin_of_right_limit
    (φ r : ℝ) (W : ℝ → ℝ)
    (hW : ContinuousWithinAt W (Set.Ioi (0 : ℝ)) 0)
    (htilt : Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds r)) :
    W 0 = r := by sorry

end AvramDividend.Classical
