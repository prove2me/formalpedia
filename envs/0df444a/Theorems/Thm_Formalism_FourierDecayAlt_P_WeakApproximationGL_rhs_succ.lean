-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_rhs_succ
-- name    : Formalism.FourierDecayAlt.P.WeakApproximationGL.rhs_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:13.991566+00:00
-- url     : https://prove2.me/theorems/128d05c7-8d49-4b3a-897f-50e59a8f045a
-- title:
--   Weak Approximation GL: rhs succ
-- statement:
--   The Weak Approximation GL construction uses the rhs succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L151-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L151-L162

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

theorem Formalism.FourierDecayAlt.P.WeakApproximationGL.rhs_succ {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1))
    (j : Fin (m + 2)) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) i.succ j =
      (if (j : ℕ) = i then t else 0) + triXY x y i.succ j := by sorry
