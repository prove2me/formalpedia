-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_phiReg_of
-- name    : Formalism.FourierDecayAlt.P.S3dx4.phiReg_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:42.679084+00:00
-- url     : https://prove2.me/theorems/ce2edecb-79ac-4188-bad7-2479f80cd44e
-- title:
--   S3dx4: phi Reg of
-- statement:
--   The S3dx4 construction uses the phi Reg of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiRegOf.lean#L20-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiRegOf.lean#L20-L91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
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

theorem Formalism.FourierDecayAlt.P.S3dx4.phiReg_of (hSch : SchurH) (hNI : NormIdSm) (hGG : GrowthG) (hDD : DecDD) (hBC : BeConv) :
    More.PhiReg := by sorry
