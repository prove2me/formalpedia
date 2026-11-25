-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliUnderIntegral_cvUnderInt_of_jWords
-- name    : Formalism.FourierDecayAlt.P.CapelliUnderIntegral.cvUnderInt_of_jWords
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:36:16.607277+00:00
-- url     : https://prove2.me/theorems/4e0ce0f8-075d-5a31-adff-1e4e0b1f3653
-- title:
--   Capelli Under Integral: cv Under Int of j Words
-- statement:
--   The Capelli Under Integral construction uses the cv Under Int of j Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliUnderIntegral.lean#L51-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliUnderIntegral.lean#L51-L92

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CapelliUnderIntegral.cvUnderInt_of_jWords : Formalism.FourierDecayAlt.JF.JWords → Formalism.FourierDecayAlt.JF.RwRho → Formalism.FourierDecayAlt.JF.CVUnderInt := by sorry
