-- Prove2me | solution 1 for jets_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:25:48.601341+00:00
-- url     : https://prove2.me/submissions/2fba4579-13d6-4d80-83f2-414d1db8f929

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_HighGOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ChainSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_SecondJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_JetsPhW
import Theorems.Thm_jets_phase_weights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.JetsPhW.One :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.1
