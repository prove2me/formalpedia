-- Prove2me | solution 1 for quotient_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:40.056725+00:00
-- url     : https://prove2.me/submissions/3d36a826-984a-4a45-b91b-0b161d44e2a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotInv
import Theorems.Thm_PI_QuotInvW_quotInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QuotInv := PI.QuotInvW.quotInv
