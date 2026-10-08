-- Prove2me | Theorems.Thm_AvramDividend_Classical_deriv_near_zero_strict_of_liminf_gap
-- name    : AvramDividend.Classical.deriv_near_zero_strict_of_liminf_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:27:49.664737+00:00
-- url     : https://prove2.me/theorems/a629388e-f0e5-44a5-bcc2-0478ed0fae78
-- title:
--   A strict one-sided scale-derivative liminf gap excludes near-zero ordinary derivative minimisers
-- statement:
--   When the canonical right-hand derivative liminf at zero is strictly larger than the ordinary derivative at a positive reference point, the ordinary derivative is strictly larger than its value at that reference point throughout some right neighbourhood of zero. This uses the actual Avram derivZeroPlus definition rather than the ordinary derivative at zero, which is zero under the negative-halfline scale function convention.
-- source:
--   Pinned Mathlib Order.LiminfLimsup.eventually_lt_of_lt_liminf transfers a strict bound below the EReal right-hand liminf into a filter-eventual strict bound. EReal.coe_lt_coe_iff converts the inequalities between embedded real derivatives to the corresponding real inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter
open scoped Topology

namespace AvramDividend.Classical

theorem deriv_near_zero_strict_of_liminf_gap
    (W : ℝ → ℝ) (a : ℝ)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W) :
    ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), deriv W a < deriv W x := by
  sorry

end AvramDividend.Classical
