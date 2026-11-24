-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_integrable_of_decay
-- name    : Formalism.FourierDecayAlt.P.JCx1.needs.integrable_of_decay
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:25.412067+00:00
-- url     : https://prove2.me/theorems/7f283ad5-222d-45fc-b3f6-7b95d81d8a60
-- title:
--   needs: integrable of decay
-- statement:
--   The needs construction uses the integrable of decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L789-L798
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L789-L798

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section

theorem Formalism.FourierDecayAlt.P.JCx1.needs.integrable_of_decay {φ : ℂ → ℂ} (hc : Continuous φ) {Cφ : ℝ}
    (hb : ∀ c, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) : Integrable φ := by sorry
