-- Prove2me | solution 1 for wwInjective_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:14.420278+00:00
-- url     : https://prove2.me/submissions/d47abc36-df18-4460-b477-4bfefa8073b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwInjective
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_InstFintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WwInjective
import Theorems.Thm_PI_WwInjectiveWork_wwInjective_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
