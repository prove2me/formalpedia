-- Prove2me | solution 1 for witt_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:45.98307+00:00
-- url     : https://prove2.me/submissions/7c6254b4-0e7f-4057-b345-c6965bbc40ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittSubstitution_CoeffMapMem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WfSubst
import Theorems.Thm_PI_WfSubstProof_wfSubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WfSubst := PI.WfSubstProof.wfSubst
