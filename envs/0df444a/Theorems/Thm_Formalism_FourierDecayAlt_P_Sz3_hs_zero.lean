-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_zero
-- name    : Formalism.FourierDecayAlt.P.Sz3.hs_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:24.476297+00:00
-- url     : https://prove2.me/theorems/0b1cf442-8382-5778-8bb5-dedcf36151a4
-- title:
--   Sz3: hs zero
-- statement:
--   The Sz3 construction uses the hs zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L237-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L237-L237

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.hs_zero : hs 0 = 0 := by sorry
