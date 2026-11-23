-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_rhs_zero
-- name    : Formalism.FourierDecayAlt.P.WeakApproximationGL.rhs_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:54.703157+00:00
-- url     : https://prove2.me/theorems/997e284f-0cc4-4f63-b22a-8224038c3d42
-- title:
--   Weak Approximation GL: rhs zero
-- statement:
--   The Weak Approximation GL construction uses the rhs zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L146-L149

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

theorem Formalism.FourierDecayAlt.P.WeakApproximationGL.rhs_zero {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {j : Fin (m + 2)} (h : 0 < j) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) 0 j =
      triXY x y 0 j := by sorry
