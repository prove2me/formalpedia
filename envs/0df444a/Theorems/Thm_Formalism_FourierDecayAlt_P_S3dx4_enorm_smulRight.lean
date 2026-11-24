-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_enorm_smulRight
-- name    : Formalism.FourierDecayAlt.P.S3dx4.enorm_smulRight
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:17.800808+00:00
-- url     : https://prove2.me/theorems/7765a247-18c7-4917-ba8c-515ad48d7332
-- title:
--   S3dx4: enorm smul Right
-- statement:
--   The S3dx4 construction uses the enorm smul Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerBound.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerBound.lean#L26-L30

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.enorm_smulRight {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (a : E) (b : F) :
    ‖(innerSL ℂ a).smulRight b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by sorry
