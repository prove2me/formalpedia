-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_exp_generates
-- name    : Formalism.FourierDecayAlt.P.exp_generates
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:15:54.227199+00:00
-- url     : https://prove2.me/theorems/2bc88785-ba68-42f6-982b-84ffe4c285d1
-- title:
--   P: exp generates
-- statement:
--   The P construction uses the exp generates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L325-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L325-L374

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open HermitianFormRankFour

theorem Formalism.FourierDecayAlt.P.exp_generates : Formalism.FourierDecayAlt.Qr.ExpGen := by sorry
