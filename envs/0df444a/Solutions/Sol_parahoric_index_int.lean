-- Prove2me | solution 1 for parahoric_index_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:43.781839+00:00
-- url     : https://prove2.me/submissions/25ed65b2-2765-44f5-9795-fccac07234b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ParahoricIdxZ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_IdxStep
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ParahoricIdxZ
import Theorems.Thm_PI_ParahoricIdxZ_W_cardStep
import Theorems.Thm_PI_ParahoricIdxZ_W_idxStep
import Theorems.Thm_PI_ParahoricIdxZ_W_parahoricIdxZ_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ParahoricIdxZ :=
  PI.ParahoricIdxZ.W.parahoricIdxZ_of PI.ParahoricIdxZ.W.idxStep PI.ParahoricIdxZ.W.cardStep
