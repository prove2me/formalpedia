-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_positionDiff
-- name    : Formalism.FourierDecayAlt.P.positionDiff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:02.817039+00:00
-- url     : https://prove2.me/theorems/111c06da-d482-50a4-9aa7-96cefe6490e4
-- title:
--   P: position Diff
-- statement:
--   The P construction uses the position Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L102-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L102-L125

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.positionDiff : Formalism.FourierDecayAlt.Sz.PositionDiff := by sorry
