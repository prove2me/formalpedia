-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_norm_apply_le
-- name    : Formalism.FourierDecayAlt.P.Ux11.norm_apply_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:57.121327+00:00
-- url     : https://prove2.me/theorems/de9e85f1-a02e-4c39-8274-00260eb37fc6
-- title:
--   Ux11: norm apply le
-- statement:
--   The Ux11 construction uses the norm apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L137-L141

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.Ux11.norm_apply_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (h : X) (hh : ‖h‖ ≤ 1) :
    ‖ContinuousLinearMap.apply ℝ F h‖ ≤ 1 := by sorry
