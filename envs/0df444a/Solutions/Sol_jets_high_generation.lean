-- Prove2me | solution 1 for jets_high_generation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:01:10.17595+00:00
-- url     : https://prove2.me/submissions/d5f9c004-7fdc-4fcc-9540-cd6ee59ae169

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_HighGOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ChainSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_SecondJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_JetsPhW
import Theorems.Thm_PI_JetsPhW_W_derivative_chain_rule
import Theorems.Thm_PI_JetsPhW_W_derivative_integral
import Theorems.Thm_PI_JetsPhW_W_derivative_self
import Theorems.Thm_PI_JetsPhW_W_evaluation_at_zero
import Theorems.Thm_PI_JetsPhW_W_highG_of
import Theorems.Thm_PI_JetsPhW_W_jet_derivative_integrality
import Theorems.Thm_PI_JetsPhW_W_log_derivative_integral_jet_integrality
import Theorems.Thm_PI_JetsPhW_W_pderiv_subst_ne
import Theorems.Thm_PI_JetsPhW_W_pderiv_subst_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.JetsPhW.HighG :=
  PI.JetsPhW.W.highG_of PI.JetsPhW.W.derivative_chain_rule PI.JetsPhW.W.derivative_self
    PI.JetsPhW.W.pderiv_subst_ne PI.JetsPhW.W.pderiv_subst_self PI.JetsPhW.W.evaluation_at_zero
    PI.JetsPhW.W.jet_derivative_integrality PI.JetsPhW.W.log_derivative_integral_jet_integrality PI.JetsPhW.W.derivative_integral
