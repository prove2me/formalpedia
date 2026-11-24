-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_irredCap_of
-- name    : Formalism.FourierDecayAlt.P.qr_irredCap_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:17.983606+00:00
-- url     : https://prove2.me/theorems/6055a333-f780-4db5-9665-c7858bfd0ac7
-- title:
--   P: qr irred Cap of
-- statement:
--   The P construction uses the qr irred Cap of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L213-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L213-L232

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.qr_irredCap_of : Qr.ExistsSingMax → Qr.CapSing → Qr.CapStab → Qr.SubRel → Qr.TopWeightSing → Qr.DualMinor →
    Qr.SpanTop → Qr.MultOne → Qr.Decomp → Qr.CapIndep → Qr.IrredCap := by sorry
