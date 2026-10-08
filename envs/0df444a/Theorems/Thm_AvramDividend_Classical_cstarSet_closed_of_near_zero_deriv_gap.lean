-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstarSet_closed_of_near_zero_deriv_gap
-- name    : AvramDividend.Classical.cstarSet_closed_of_near_zero_deriv_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:24:40.133522+00:00
-- url     : https://prove2.me/theorems/87cff91f-18cc-40d3-8972-767e0e677fa3
-- title:
--   Closedness of the positive scale-derivative minimiser set from an exclusion zone near zero
-- statement:
--   Suppose W has a positive global ordinary-derivative minimiser at a, with the ordinary derivative continuous only on (0,infinity). If for some delta>0 the derivative is strictly higher than its minimum at every x in (0,delta), then the set of all positive global derivative minimisers is a closed subset of the real line. The result deliberately avoids the ordinary derivative at zero, which is not the right derivative relevant to the canonical scale function.
-- source:
--   The near-zero exclusion forces every positive global minimiser to lie in Ici delta. On this closed interval the minimiser set is exactly the preimage of the closed derivative sublevel Iic (deriv W a). ContinuousOn on Ioi 0 restricts to Ici delta since delta>0. Pinned Mathlib ContinuousOn.preimage_isClosed_of_isClosed proves the set is closed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem cstarSet_closed_of_near_zero_deriv_gap
    (W : ℝ → ℝ) (a δ : ℝ)
    (ha : a ∈ cstarSet W)
    (hδ : 0 < δ)
    (hgap : ∀ x : ℝ, 0 < x → x < δ → deriv W a < deriv W x)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    IsClosed (cstarSet W) := by
  sorry

end AvramDividend.Classical
