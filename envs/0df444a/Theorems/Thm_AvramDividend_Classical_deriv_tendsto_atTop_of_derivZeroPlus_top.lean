-- Prove2me | Theorems.Thm_AvramDividend_Classical_deriv_tendsto_atTop_of_derivZeroPlus_top
-- name    : AvramDividend.Classical.deriv_tendsto_atTop_of_derivZeroPlus_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T20:43:53.90748+00:00
-- url     : https://prove2.me/theorems/40fd1c21-c1dc-4d6b-afb1-07cb3d8c6779
-- title:
--   Infinite extended right-derivative liminf implies real derivative divergence at the origin
-- statement:
--   The canonical Avram definition derivZeroPlus W is the EReal-valued right-hand liminf of ordinary real derivatives. If it equals plus infinity, then the real function deriv W tends to plus infinity as x approaches zero from the right. This exact bridge turns the source-faithful extended derivative condition into the filter limit required by the compact-away-from-zero cstar attainment theorem, without adding a smoothness or endpoint regularity assumption.
-- source:
--   Pinned Mathlib Order/LiminfLimsup.lean:799 theorem eventually_lt_of_lt_liminf gives eventual strict lower bounds for an EReal-valued liminf. From derivZeroPlus W=top, each real b embedded into EReal is strictly less than the liminf, yielding eventually b<deriv W x. Convert the EReal inequality back to real and apply tendsto_atTop. This is not the countable-intersection lemma liminf_eq_top, which is unsuitable for right-neighbourhood filters.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter
open scoped Topology ENNReal

namespace AvramDividend.Classical

theorem deriv_tendsto_atTop_of_derivZeroPlus_top (W : ℝ → ℝ)
    (h : derivZeroPlus W = ⊤) :
    Filter.Tendsto (deriv W) (𝓝[>] (0 : ℝ)) Filter.atTop := by
  sorry

end AvramDividend.Classical
