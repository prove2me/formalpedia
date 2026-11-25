-- Prove2me | solution 1 for trace_dual_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:28.93188+00:00
-- url     : https://prove2.me/submissions/0a4f97c0-fd87-4364-8908-db1ff5d5445b

import Definitions.Def_Formalism_PeriodIntegrals_TrDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_Imports
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TrDualLoc
import Theorems.Thm_PI_CntNotIntW_tensorLiftSurjective
import Theorems.Thm_PI_TrDualLocW_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.TrDualLoc.Stmt := by
  intro K _ _ p _ Fp _ _ _ _ _ hc hfin ι hd _ t ht c hcO
  haveI : CharZero Fp :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp).injective
  exact PI.TrDualLocW.main hc hfin ι (PI.CntNotIntW.tensorLiftSurjective K _ Fp hc hfin ι hd) t ht c hcO
