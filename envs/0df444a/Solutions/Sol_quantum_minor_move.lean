-- Prove2me | solution 1 for quantum_minor_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:23.283265+00:00
-- url     : https://prove2.me/submissions/046b8b41-1051-4e45-a3e8-ab2f7e15f7cb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_move_operator_covariance
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_move_operator_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QmMove := ⟨PI.UnitaryGroupMassFormula.QmMove.move_operator_vector, PI.UnitaryGroupMassFormula.QmMove.move_operator_covariance⟩
