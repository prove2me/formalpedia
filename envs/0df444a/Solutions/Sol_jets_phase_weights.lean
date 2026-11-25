-- Prove2me | solution 1 for jets_phase_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:34.967488+00:00
-- url     : https://prove2.me/submissions/3c0586a5-e5d2-4da9-b6a9-41e96db495ef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_HighGOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ChainSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_SecondJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_JetsPhW
import Theorems.Thm_jets_high_generation
import Theorems.Thm_PI_JetsPhW_Inv_inverse_omega_holds
import Theorems.Thm_PI_JetsPhW_Low_firstJetIntegralGeneral_holds
import Theorems.Thm_PI_JetsPhW_Low_secondJetIntegralGeneral_holds
import Theorems.Thm_PI_JetsPhW_W_glue_holds_var
import Theorems.Thm_UpperTheory_Reformulated_B_Gwa1_inverse_omega_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.JetsPhW.Target :=
  PI.JetsPhW.W.glue_holds_var PI.JetsPhW.Inv.inverse_omega_holds jets_high_generation
    PI.JetsPhW.Low.firstJetIntegralGeneral_holds PI.JetsPhW.Low.secondJetIntegralGeneral_holds
