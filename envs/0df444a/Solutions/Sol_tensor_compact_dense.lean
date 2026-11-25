-- Prove2me | solution 1 for tensor_compact_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:24.890746+00:00
-- url     : https://prove2.me/submissions/50a29f63-2594-4099-9d07-8bebbbf5943a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TensCpctDen
import Theorems.Thm_PI_tensCpctDen_of
import Theorems.Thm_compactBounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.TensCpctDen := PI.tensCpctDen_of compactBounded
