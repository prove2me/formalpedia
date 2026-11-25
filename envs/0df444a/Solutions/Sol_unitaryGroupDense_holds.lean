-- Prove2me | solution 1 for unitaryGroupDense_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:51.998853+00:00
-- url     : https://prove2.me/submissions/3b0beadf-9330-43a4-a017-cdc243a9efcd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_VanishInvertible
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Decomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryDense
import Theorems.Thm_productFramesDense_holds
import Theorems.Thm_unitaryDense_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UnitaryDense := unitaryDense_of productFramesDense_holds
