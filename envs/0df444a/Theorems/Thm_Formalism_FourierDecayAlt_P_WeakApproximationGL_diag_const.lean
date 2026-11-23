-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_diag_const
-- name    : Formalism.FourierDecayAlt.P.WeakApproximationGL.diag_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:08.893281+00:00
-- url     : https://prove2.me/theorems/4544b5be-745f-4004-8120-aa3ff5a0cd7e
-- title:
--   Weak Approximation GL: diag const
-- statement:
--   The Weak Approximation GL construction uses the diag const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean#L232-L238

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

theorem Formalism.FourierDecayAlt.P.WeakApproximationGL.diag_const (m : ℕ) (z : ℂ) :
    Matrix.diagonal (Fin.cons z (fun _ : Fin (m + 1) => z) : Fin (m + 2) → ℂ) =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by sorry
