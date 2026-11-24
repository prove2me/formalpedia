-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ckOn_zero_of_contOn
-- name    : Formalism.FourierDecayAlt.P.S3dx4.ckOn_zero_of_contOn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:07.048349+00:00
-- url     : https://prove2.me/theorems/b796043e-a936-41ad-ba99-bad6180c4f1b
-- title:
--   S3dx4: ck On zero of cont On
-- statement:
--   The S3dx4 construction uses the ck On zero of cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CkOnZeroOfContOn.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CkOnZeroOfContOn.lean#L19-L31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
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

theorem Formalism.FourierDecayAlt.P.S3dx4.ckOn_zero_of_contOn {k r : ℕ} (f : Mx k r → ℂ) (hf : ContinuousOn f (B.GV k r)) :
    B.CkOn ((0 : ℕ) : ℕ∞) (B.GV k r) (fun g => f g • (1 : ℂ →L[ℂ] ℂ)) := by sorry
