-- Prove2me | solution 1 for dvProjA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:52.536502+00:00
-- url     : https://prove2.me/submissions/7dd7c06a-9c95-4de0-a5d3-e985dd54904a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_IdxEqLen
import Theorems.Thm_PI_Dv_ProjAW_projA_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
theorem _root_.solution (hI : PI.Dv.IdxCalc) : PI.Dv.ProjA := PI.Dv.ProjAW.projA_of hI
