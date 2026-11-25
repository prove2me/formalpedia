-- Prove2me | solution 1 for ordRelativeDet_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:15:27.047268+00:00
-- url     : https://prove2.me/submissions/e886e16e-b7d8-48b0-845f-35a10de3753a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerDetFin
import Theorems.Thm_PI_KerDetFinW_detOrdFin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
