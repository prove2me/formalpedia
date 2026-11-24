-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_wMat_mulVec_apply
-- name    : Formalism.FourierDecayAlt.P.WeakApproximationGL.wMat_mulVec_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:24.009644+00:00
-- url     : https://prove2.me/theorems/4bd1493c-ae95-418e-89f1-13a6975134fe
-- title:
--   Weak Approximation GL: w Mat mul Vec apply
-- statement:
--   The Weak Approximation GL construction uses the w Mat mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L164-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L164-L165

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

theorem Formalism.FourierDecayAlt.P.WeakApproximationGL.wMat_mulVec_apply {n : ℕ} (B : Fin n → ℂ) (i : Fin n) : (wMat n *ᵥ B) i = B i.rev := by sorry
