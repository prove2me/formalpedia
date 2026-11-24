-- Prove2me | solution 1 for contraction_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:15.036784+00:00
-- url     : https://prove2.me/submissions/6255ef1b-17cb-461b-a874-2277c2c2609f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnAdapted
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_chat2Adapted_of
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_chatAdapted_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by
  intro hcov
  exact ⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩
