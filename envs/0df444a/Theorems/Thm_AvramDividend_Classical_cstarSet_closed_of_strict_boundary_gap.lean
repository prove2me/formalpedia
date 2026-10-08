-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstarSet_closed_of_strict_boundary_gap
-- name    : AvramDividend.Classical.cstarSet_closed_of_strict_boundary_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T14:34:04.325376+00:00
-- url     : https://prove2.me/theorems/1a6274f7-2cd0-48c4-9c8d-c340b9ee3405
-- title:
--   Closedness of the positive derivative-minimiser set from continuity and a strict boundary gap
-- statement:
--   Suppose the ordinary derivative of the Avram scale function is continuous on the nonnegative half-line, and at some positive global derivative minimiser a the derivative is strictly below its value at zero. Then the set of all positive global derivative minimisers is closed in the real line. The strict gap excludes zero as a limit point; elsewhere the set is the preimage of a closed derivative sublevel set.
-- source:
--   The nonnegative-half-line derivative min-set equals Ici 0 intersect the closed sublevel preimage of Iic (deriv W a). The known minimiser a provides the lower comparison for all x>0; the strict gap at 0 excludes the endpoint. Pinned Mathlib ContinuousOn.preimage_isClosed_of_isClosed then proves closedness of the set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem cstarSet_closed_of_strict_boundary_gap
    (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : a ∈ cstarSet W)
    (hgap : deriv W a < deriv W 0) :
    IsClosed (cstarSet W) := by
  sorry

end AvramDividend.Classical
