-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_rpow_bound
-- name    : Formalism.FourierDecayAlt.P.S3dx4.rpow_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:21.008419+00:00
-- url     : https://prove2.me/theorems/34bc1fc3-6de5-4d84-b4e5-06948177aca6
-- title:
--   S3dx4: rpow bound
-- statement:
--   The S3dx4 construction uses the rpow bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbConvDDOfDecDD.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbConvDDOfDecDD.lean#L42-L48

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

theorem Formalism.FourierDecayAlt.P.S3dx4.rpow_bound (t C a : ℝ) (ht : 0 ≤ t) (ha : a ≠ 0) : t ^ a * (C * t ^ (-a)) ≤ |C| := by sorry
