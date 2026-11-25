-- Prove2me | solution 1 for quantum_v_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:49.223503+00:00
-- url     : https://prove2.me/submissions/eba530c3-1e6d-4bc3-a216-c1fa3fba957c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnVMonic
import Theorems.Thm_qnVMonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.VMonic := qnVMonic
