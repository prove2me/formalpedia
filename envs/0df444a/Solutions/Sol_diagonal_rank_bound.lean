-- Prove2me | solution 1 for diagonal_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:17.536594+00:00
-- url     : https://prove2.me/submissions/0f5fa216-9eea-4f26-b39a-b95d57066bcb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiagRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalRank_DetOneSubPNe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DiagRank
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiagRank_diagRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.DiagRank := PI.UnitaryGroupMassFormula.DiagRank.diagRank
