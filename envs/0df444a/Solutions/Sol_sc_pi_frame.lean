-- Prove2me | solution 1 for sc_pi_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:04:13.153743+00:00
-- url     : https://prove2.me/submissions/7dc16d09-72af-4d89-bb25-c77229357fe7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameHypothesesRankZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScPiFrame
import Theorems.Thm_PI_ScPiFrameW_frame_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
