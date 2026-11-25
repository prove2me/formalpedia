-- Prove2me | solution 1 for zerosWindow_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:27.293468+00:00
-- url     : https://prove2.me/submissions/e2846b5f-fe5a-4369-9356-d8e1a94315b6

import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_AnalyticInputs
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ZerosWindow
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ExplicitFormula
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_ExplicitFormula
import Theorems.Thm_chk_lBoundRight
import Theorems.Thm_chk_lInvRight
import Theorems.Thm_chk_zetaBoundRight
import Theorems.Thm_zerosWindow_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ZerosWindow :=
  zerosWindow_of chk_lBoundRight chk_zetaBoundRight chk_lInvRight
