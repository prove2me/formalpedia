-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SchurNormSquareBounds_norm_sq_sum_le
-- name    : Formalism.FourierDecayAlt.P.SchurNormSquareBounds.norm_sq_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:04.532182+00:00
-- url     : https://prove2.me/theorems/76d5a724-1d67-4cfa-9940-1837438ec5d9
-- title:
--   Schur Norm Square Bounds: norm sq sum le
-- statement:
--   The Schur Norm Square Bounds construction uses the norm sq sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RowNormSquareBounds.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RowNormSquareBounds.lean#L7-L20

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RowNormSquareBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SchurNormSquareBounds
open Finset

theorem Formalism.FourierDecayAlt.P.SchurNormSquareBounds.norm_sq_sum_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type}
    [DecidableEq ι] (T : Finset ι) (V : ι → H) :
    ‖∑ t ∈ T, V t‖ ^ 2 ≤
      (∑ t ∈ T, ‖V t‖ ^ 2) + ∑ t ∈ T, ∑ t' ∈ T.erase t, ‖inner ℂ (V t) (V t')‖ := by sorry
