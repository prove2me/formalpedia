-- Prove2me | solution 1 for ordRelativeDet_independence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:52.528156+00:00
-- url     : https://prove2.me/submissions/8b48aab3-0de9-439e-a591-bff47275fdbd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerDetOrd
import Theorems.Thm_PI_KerIso_DetOrdW_detOrdIndep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerIso.DetOrdIndep :=
  PI.KerIso.DetOrdW.detOrdIndep
