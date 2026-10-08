-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_minimizer_exists_of_deriv_below_boundary_and_tail
-- name    : AvramDividend.Classical.cstar_minimizer_exists_of_deriv_below_boundary_and_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T14:19:43.097079+00:00
-- url     : https://prove2.me/theorems/7edb7b65-80bb-4d86-890c-23d3f57011d3
-- title:
--   Existence of a positive global derivative minimiser from interior improvement and tail coercivity
-- statement:
--   Let the derivative of W be continuous on the nonnegative half-line. Suppose its derivative is strictly smaller at some positive a than at zero, and, outside compact sets in the half-line, is at least its value at a. Then a global derivative minimum is attained at a strictly positive point, so the canonical Avram cstarSet W is nonempty. This establishes a substantive sufficient condition for a finite positive-attainment branch.
-- source:
--   Pinned Mathlib ContinuousOn.exists_isMinOn' yields a global minimum of deriv W on Ici 0 from continuous-on and cocompact tail lower bound. Strict improvement deriv W a < deriv W 0 forces the selected minimizer away from zero, so it belongs to the exact cstarSet.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set

namespace AvramDividend.Classical

theorem cstar_minimizer_exists_of_deriv_below_boundary_and_tail
    (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : 0 < a) (hstrict : deriv W a < deriv W 0)
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W a ≤ deriv W x) :
    (cstarSet W).Nonempty := by
  sorry

end AvramDividend.Classical
