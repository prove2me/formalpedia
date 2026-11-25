-- Prove2me | solution 1 for local_endomorphism_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:03:55.543641+00:00
-- url     : https://prove2.me/submissions/7becfe93-5723-464e-b547-3c299d67360b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_HenselRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LocalEnd
import Theorems.Thm_PI_LocalEndW_henselRoot
import Theorems.Thm_PI_LocalEndW_intOfHensel
import Theorems.Thm_PI_LocalEndW_localEndHomeo_of_three
import Theorems.Thm_PI_LocalEndW_valOfInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LocalEndHomeo :=
  PI.LocalEndW.localEndHomeo_of_three PI.LocalEndW.henselRoot PI.LocalEndW.intOfHensel PI.LocalEndW.valOfInt
