-- Prove2me | solution 1 for squarefree_root_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:30.712924+00:00
-- url     : https://prove2.me/submissions/34ec5e3b-fa85-4c89-8d67-f788a896d2c0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_ArithP
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SqfRootShift
import Theorems.Thm_PI_SqfRootShift_W_arithP
import Theorems.Thm_PI_SqfRootShift_W_claim_of
import Theorems.Thm_PI_SqfRootShift_W_countP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SqfRootShift.Claim :=
  PI.SqfRootShift.W.claim_of PI.SqfRootShift.W.countP PI.SqfRootShift.W.arithP
