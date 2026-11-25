-- Prove2me | solution 1 for tiltSurjectiveOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:24.657633+00:00
-- url     : https://prove2.me/submissions/0305d9ba-d895-4216-ba67-dcc599df4880

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ASGlue
import Theorems.Thm_PI_ArtSch_Glue_tiltGlue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ArtSch.TiltGlue := PI.ArtSch.Glue.tiltGlue
