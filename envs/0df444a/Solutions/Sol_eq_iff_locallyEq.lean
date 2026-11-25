-- Prove2me | solution 1 for eq_iff_locallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:56.460049+00:00
-- url     : https://prove2.me/submissions/1b203cca-b144-49c1-90ba-7c693335d798

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_AvoidP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_EpNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LocLatEq
import Theorems.Thm_PI_LocLatEq_W_avoidP
import Theorems.Thm_PI_LocLatEq_W_coreP_of_unitP_avoidP_intP
import Theorems.Thm_PI_LocLatEq_W_intP
import Theorems.Thm_PI_LocLatEq_W_locLatEq_of
import Theorems.Thm_PI_LocLatEq_W_unitP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LocLatEq.Stmt :=
  PI.LocLatEq.W.locLatEq_of PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP
    (PI.LocLatEq.W.coreP_of_unitP_avoidP_intP PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP PI.LocLatEq.W.intP)
