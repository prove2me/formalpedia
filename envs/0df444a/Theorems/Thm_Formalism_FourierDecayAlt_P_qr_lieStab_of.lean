-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_lieStab_of
-- name    : Formalism.FourierDecayAlt.P.qr_lieStab_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:35:43.135124+00:00
-- url     : https://prove2.me/theorems/73129a67-f198-4577-935a-a632a8f14089
-- title:
--   P: qr lie Stab of
-- statement:
--   The P construction uses the qr lie Stab of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L270-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean#L270-L289

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.qr_lieStab_of : Formalism.FourierDecayAlt.Qr.ExpGen → Formalism.FourierDecayAlt.Qr.PiExp → Formalism.FourierDecayAlt.Qr.EcLie → Formalism.FourierDecayAlt.Qr.LieStab := by sorry
