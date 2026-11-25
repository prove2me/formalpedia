-- Prove2me | solution 1 for isometry_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:01:04.580873+00:00
-- url     : https://prove2.me/submissions/d2b5a5f7-40bf-483a-a412-ab9513b33557

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoScaleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryScaleCount_CardEqSumColLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsoScaleA
import Theorems.Thm_PI_IsoScaleA_UnitaryGroupMassFormula_isoScaleA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.IsoScaleA.IsoScaleA := PI.IsoScaleA.UnitaryGroupMassFormula.isoScaleA
