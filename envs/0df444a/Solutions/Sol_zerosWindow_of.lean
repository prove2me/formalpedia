-- Prove2me | solution 1 for zerosWindow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:25:57.092239+00:00
-- url     : https://prove2.me/submissions/6091f486-6f27-43de-b56c-2cf038419ba5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindow
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ZerosWindow
import Theorems.Thm_PI_ZW_transfer
import Theorems.Thm_PI_ZW_zerosWindow_of_transfer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI
