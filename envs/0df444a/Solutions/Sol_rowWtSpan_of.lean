-- Prove2me | solution 1 for rowWtSpan_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:13:59.800954+00:00
-- url     : https://prove2.me/submissions/e4ef3531-80ec-4119-b8f9-023d87892d24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowWtSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowWeightSpan_RowWtSpanOfBideterminant
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_RowWtSpan
import Theorems.Thm_PI_RWS_rowWtSpan_of_bideterminant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
