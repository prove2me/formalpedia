-- Prove2me | solution 1 for exists_gaugeNormalizedStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:44.217471+00:00
-- url     : https://prove2.me/submissions/64aa0af7-280a-4dd5-91c7-be7af30b2ddb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ExistsGaugeNormalizedStabilizer
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_gauge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
