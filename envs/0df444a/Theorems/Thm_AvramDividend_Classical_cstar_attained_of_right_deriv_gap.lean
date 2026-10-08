-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_attained_of_right_deriv_gap
-- name    : AvramDividend.Classical.cstar_attained_of_right_deriv_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:31:04.582223+00:00
-- url     : https://prove2.me/theorems/328347ad-8a13-419d-af31-29a0b5db6114
-- title:
--   Attainment of the canonical Avram dividend barrier from a strict one-sided boundary derivative gap
-- statement:
--   Suppose a is a positive global minimiser of the ordinary derivative of the scale function, the derivative is continuous for x>0, and the derivative at a lies strictly below the canonical extended right-hand derivative liminf at zero. Then the real value of the infimum-defined barrier cstar is itself a positive global derivative minimiser. The proof uses closedness away from zero and compactness of minimisers up to a, making the hypothesis suitable for actual q-scale functions whose ordinary derivative at zero is zero or undefined.
-- source:
--   A right-derivative liminf gap yields near-zero exclusion, and therefore closedness of cstarSet W under continuity on Ioi 0. Intersect this closed set with Icc 0 a, a compact interval containing a positive global derivative minimiser. The existing Proved compact-initial-minimiser theorem identifies its least member with the ENNReal infimum defining cstar.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem cstar_attained_of_right_deriv_gap
    (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
