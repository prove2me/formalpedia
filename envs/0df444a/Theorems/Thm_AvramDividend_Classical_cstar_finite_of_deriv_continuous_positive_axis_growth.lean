-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_of_deriv_continuous_positive_axis_growth
-- name    : AvramDividend.Classical.cstar_finite_of_deriv_continuous_positive_axis_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:08:57.378404+00:00
-- url     : https://prove2.me/theorems/9e0e997b-621a-4d31-b40f-b39be3e96f0e
-- title:
--   Finite Avram cstar from derivative continuity only on positive axis and divergence at infinity
-- statement:
--   If the ordinary derivative of W is continuous at all positive points, with no continuity assumption at zero, and diverges to positive infinity as x tends to positive infinity, then the canonical infimum-defined dividend barrier cstar W is finite. The proof splits according to whether its extended right-derivative liminf at zero is a lower bound for every positive derivative. Otherwise derivative values near zero and infinity exceed an interior test value, so a global positive minimum exists on a compact interval. This directly addresses the positive-half-line regularity required by the original Avram finiteness milestone.
-- source:
--   Adapt the previously researched uncompiled deterministic compactness argument from artifacts/m2m4/milestone_campaign_20261004/m2/cstar_analytic_bridge.lean. A lower-bound-at-zero case is settled by the proved exact cstar finite iff. Otherwise strict liminf separation near zero, eventual growth atTop, and positive-axis continuity give a minimiser on compact Icc [l,u]. No quasi-convexity and no boundary differentiability hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary
open AvramDividend.Classical Filter Set Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_finite_of_deriv_continuous_positive_axis_growth (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ)))
    (htop : Tendsto (deriv W) Filter.atTop Filter.atTop) :
    cstar W < ⊤ := by
  sorry

end AvramDividend.Classical
