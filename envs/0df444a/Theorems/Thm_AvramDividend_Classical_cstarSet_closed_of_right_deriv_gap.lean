-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstarSet_closed_of_right_deriv_gap
-- name    : AvramDividend.Classical.cstarSet_closed_of_right_deriv_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:30:34.725343+00:00
-- url     : https://prove2.me/theorems/57f7833c-0ec6-4347-909e-7d97b5acf17c
-- title:
--   The Avram positive derivative-minimiser set is closed under a strict one-sided derivative gap
-- statement:
--   Let a be a positive global minimiser of the canonical scale-function derivative. If the real derivative is continuous on (0,infinity) and is strictly less at a than the one-sided right-derivative liminf derivZeroPlus W at zero, then the whole positive global-minimiser set cstarSet W is closed. Unlike the earlier gap relative to the ordinary derivative at zero, this hypothesis is meaningful for actual spectrally negative Levy scale functions and can include an infinite right derivative.
-- source:
--   Pinned Mathlib eventually_lt_of_lt_liminf derives a strict derivative inequality on the right neighbourhood filter. Pinned mem_nhdsGT_iff_exists_Ioo_subset extracts a positive delta with a strict gap for all x in (0,delta). This excludes zero as an accumulation point of derivative minimisers. Apply the standalone closedness theorem from a near-zero exclusion interval and continuity on Ioi 0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter
open scoped Topology

namespace AvramDividend.Classical

theorem cstarSet_closed_of_right_deriv_gap
    (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    IsClosed (cstarSet W) := by
  sorry

end AvramDividend.Classical
