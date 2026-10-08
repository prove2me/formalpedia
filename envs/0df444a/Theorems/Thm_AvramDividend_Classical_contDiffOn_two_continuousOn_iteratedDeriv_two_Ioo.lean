-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_two_continuousOn_iteratedDeriv_two_Ioo
-- name    : AvramDividend.Classical.contDiffOn_two_continuousOn_iteratedDeriv_two_Ioo
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:11:18.749991+00:00
-- url     : https://prove2.me/theorems/50038af0-1427-4056-8453-052e4e7fd956
-- title:
--   A C2 function has a continuous second iterated derivative on an open interval
-- statement:
--   A real function W that is C2 on the open interval (0,a) has a continuous ordinary second iterated derivative on that interval. Mathlib's ContDiffOn.continuousOn_iteratedDerivWithin proves continuity of the within-set derivative; on an open interval iteratedDerivWithin and ordinary iteratedDeriv agree. This closes the Gaussian differential regularity component needed to establish continuity of the Levy generator residual.
-- source:
--   Pinned Mathlib ContDiffOn.continuousOn_iteratedDerivWithin and iteratedDerivWithin_of_isOpen.

import Mathlib

open MeasureTheory Set

namespace AvramDividend.Classical

theorem contDiffOn_two_continuousOn_iteratedDeriv_two_Ioo
    (W : ℝ → ℝ) (a : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn (iteratedDeriv 2 W) (Ioo 0 a) := by sorry

end AvramDividend.Classical
