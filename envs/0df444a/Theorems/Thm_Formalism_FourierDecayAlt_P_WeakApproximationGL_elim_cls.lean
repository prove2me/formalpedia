-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_elim_cls
-- name    : Formalism.FourierDecayAlt.P.WeakApproximationGL.elim_cls
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:55.079566+00:00
-- url     : https://prove2.me/theorems/529e7c6c-ee5f-467b-9a0f-0eec66777c61
-- title:
--   Weak Approximation GL: elim cls
-- statement:
--   The Weak Approximation GL construction uses the elim cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L30-L36

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

theorem Formalism.FourierDecayAlt.P.WeakApproximationGL.elim_cls {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1)) (j : Fin (m + 2))
    (h : i.succ ≤ j) : Sum.elim x y (cls i j h) = triXY x y i.succ j := by sorry
