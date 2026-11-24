-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_redOf_bijective
-- name    : Formalism.FourierDecayAlt.P.WeakApproximationGL.redOf_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:15.79626+00:00
-- url     : https://prove2.me/theorems/98db31bf-9bd9-44d5-86a7-d03d30b7f629
-- title:
--   Weak Approximation GL: red Of bijective
-- statement:
--   The Weak Approximation GL construction uses the red Of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L118-L122

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

theorem Formalism.FourierDecayAlt.P.WeakApproximationGL.redOf_bijective (m : ℕ) : Function.Bijective (redOf m) := by sorry
