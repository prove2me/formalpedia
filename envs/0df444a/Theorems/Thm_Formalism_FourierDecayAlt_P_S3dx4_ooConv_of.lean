-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ooConv_of
-- name    : Formalism.FourierDecayAlt.P.S3dx4.ooConv_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:14.350528+00:00
-- url     : https://prove2.me/theorems/b7e6c449-9280-44b7-874e-c6e5b94d901c
-- title:
--   S3dx4: oo Conv of
-- statement:
--   The S3dx4 construction uses the oo Conv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OoConvOf.lean#L56-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OoConvOf.lean#L56-L210

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OoConvOf
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
set_option maxHeartbeats 1000000

theorem Formalism.FourierDecayAlt.P.S3dx4.ooConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGG : GrowthG) (hDD : DecDD)
    (hBC : BeConv) : More.OOConv := by sorry
