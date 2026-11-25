-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_chatFrame_of
-- name    : Formalism.FourierDecayAlt.P.qr_chatFrame_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:07.772716+00:00
-- url     : https://prove2.me/theorems/e97e5a3b-bc72-4ad0-b1a4-fc059fd4352c
-- title:
--   P: qr chat Frame of
-- statement:
--   The P construction uses the qr chat Frame of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L149-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L149-L191

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open AnisotropicColumnSums

theorem Formalism.FourierDecayAlt.P.qr_chatFrame_of : Formalism.FourierDecayAlt.Qr.FrameMinor → Formalism.FourierDecayAlt.Qr.ChatFrame := by sorry
