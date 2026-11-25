-- Prove2me | solution 1 for square_pair_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:56.447491+00:00
-- url     : https://prove2.me/submissions/79c8438e-a66f-4e1c-92f2-74c18af3824b

import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_SqPairGlueMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SqPairGlue
import Theorems.Thm_PI_SqPairW_sqPairGlue_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SqPair.PLocalAll → Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen :=
  PI.SqPairW.sqPairGlue_main
