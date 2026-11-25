-- Prove2me | solution 1 for quantum_ff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:26.095613+00:00
-- url     : https://prove2.me/submissions/edd03ee7-db6d-4e57-bf18-18b1fa8cf091

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelGeneralLinear_GlevZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnFFZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_ffZero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.FFZero := PI.UnitaryGroupMassFormula.QnFFZero.ffZero
