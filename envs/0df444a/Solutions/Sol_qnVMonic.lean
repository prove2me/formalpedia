-- Prove2me | solution 1 for qnVMonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:24.455913+00:00
-- url     : https://prove2.me/submissions/ef1cfe46-2064-4c2d-9d8f-958916b9f502

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnVMonic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_VMonicMonicShiftEvaluation_capelli_vMonic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.VMonic := Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.capelli_vMonic
