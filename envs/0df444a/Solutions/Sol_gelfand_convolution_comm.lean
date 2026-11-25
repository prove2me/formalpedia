-- Prove2me | solution 1 for gelfand_convolution_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:19:42.216974+00:00
-- url     : https://prove2.me/submissions/3f2ee3d0-f900-45c4-989e-a4d48ee99089

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_ConvComm
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GelfConv
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_convComm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UMultOne.ConvComm := PI.UnitaryGroupMassFormula.GelfConv.convComm
