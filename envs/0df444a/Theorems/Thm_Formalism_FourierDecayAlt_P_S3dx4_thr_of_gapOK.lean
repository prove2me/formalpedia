-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_thr_of_gapOK
-- name    : Formalism.FourierDecayAlt.P.S3dx4.thr_of_gapOK
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:17.449273+00:00
-- url     : https://prove2.me/theorems/62fd802e-7b85-45e2-a8c3-4ba6045d6f74
-- title:
--   S3dx4: thr of gap OK
-- statement:
--   The S3dx4 construction uses the thr of gap OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbConvDDOfDecDD.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbConvDDOfDecDD.lean#L19-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
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
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem Formalism.FourierDecayAlt.P.S3dx4.thr_of_gapOK {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : JF.TransportedAlt k r (aOf r h) 0 := by sorry
