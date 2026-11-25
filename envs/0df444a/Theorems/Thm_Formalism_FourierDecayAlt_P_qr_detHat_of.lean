-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_detHat_of
-- name    : Formalism.FourierDecayAlt.P.qr_detHat_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:09:20.656322+00:00
-- url     : https://prove2.me/theorems/b05dca1d-cee6-48b8-8d04-0ced9f3ad914
-- title:
--   P: qr det Hat of
-- statement:
--   The P construction uses the qr det Hat of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L243-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L243-L278

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
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

theorem Formalism.FourierDecayAlt.P.qr_detHat_of (hA : Formalism.FourierDecayAlt.Qr.AlgDet) (hC : Formalism.FourierDecayAlt.Qr.ChatFrame) (hR : Formalism.FourierDecayAlt.Qr.CapRGood)
    (hS : Formalism.FourierDecayAlt.Qr.LeftRightSwap) : Formalism.FourierDecayAlt.Q.DetHat := by sorry
