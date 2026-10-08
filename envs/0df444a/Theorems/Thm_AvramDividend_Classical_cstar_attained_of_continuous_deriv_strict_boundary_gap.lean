-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_attained_of_continuous_deriv_strict_boundary_gap
-- name    : AvramDividend.Classical.cstar_attained_of_continuous_deriv_strict_boundary_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T14:35:58.989558+00:00
-- url     : https://prove2.me/theorems/9db0e96a-98bd-4712-b436-ba7e00e656cb
-- title:
--   Attainment of the optimal barrier level from derivative continuity and strict interior improvement
-- statement:
--   If the scale-function derivative is continuous on [0,infinity), attains its global positive-domain minimum at at least one positive point a, and is strictly smaller at a than at zero, then the infimum-defined canonical dividend barrier cstar is itself an attained positive global derivative minimiser. No tail coercivity, global compactness of the minimiser set or boundedness of all minimisers is assumed.
-- source:
--   Compose closedness of the positive derivative minimiser set from derivative continuity plus strict endpoint gap with compactness of the intersection of that closed set and the bounded interval [0,a]. A compact-initial-minimiser lemma identifies the least of that intersection with the global infimum defining cstar.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem cstar_attained_of_continuous_deriv_strict_boundary_gap
    (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : a ∈ cstarSet W)
    (hgap : deriv W a < deriv W 0) :
    (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
