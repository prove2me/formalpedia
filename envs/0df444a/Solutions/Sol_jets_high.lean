-- Prove2me | solution 1 for jets_high
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:20.366318+00:00
-- url     : https://prove2.me/submissions/1cffef26-4325-4dc7-90d5-24164c21e94c

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

theorem _root_.solution : PI.JetsPhW.High :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).1
