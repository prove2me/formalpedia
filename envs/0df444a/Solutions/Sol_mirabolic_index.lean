-- Prove2me | solution 1 for mirabolic_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:07.177035+00:00
-- url     : https://prove2.me/submissions/75205044-c9bf-43a3-93cc-804c0b116c9e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Theorems.Thm_P2M_PI_MirabolicIndex__mirabIndex_f365ed63d8b2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.MirabIndex.MirabIndex := PI.MirabolicIndex₂.mirabIndex
