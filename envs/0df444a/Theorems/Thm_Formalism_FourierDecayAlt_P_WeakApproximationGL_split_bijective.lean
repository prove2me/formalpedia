-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_split_bijective
-- name    : Formalism.FourierDecayAlt.P.WeakApproximationGL.split_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:59.139327+00:00
-- url     : https://prove2.me/theorems/d6deb1eb-f9d8-47f1-aad4-d905459250ab
-- title:
--   Weak Approximation GL: split bijective
-- statement:
--   The Weak Approximation GL construction uses the split bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L95-L104

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5

theorem Formalism.FourierDecayAlt.P.WeakApproximationGL.split_bijective (m : ℕ) : Function.Bijective (split m) := by sorry
