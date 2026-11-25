-- Prove2me | solution 1 for quantum_minor_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:11.667498+00:00
-- url     : https://prove2.me/submissions/3130b63b-fe0f-429c-b3f6-ad3483b6d7f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftQuantumMinor_QuantumMinorLeftHermitian
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnMinorLeft
import Theorems.Thm_qnMinorLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.QMinorLeftH := qnMinorLeft
