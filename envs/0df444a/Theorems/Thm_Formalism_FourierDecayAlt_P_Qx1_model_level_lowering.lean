-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx1_model_level_lowering
-- name    : Formalism.FourierDecayAlt.P.Qx1.model_level_lowering
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:05.278826+00:00
-- url     : https://prove2.me/theorems/e2c50a4d-df11-4e32-8fc7-2178ae0ae141
-- title:
--   Qx1: model level lowering
-- statement:
--   The Qx1 construction uses the model level lowering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelLevelMultiplier.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelLevelMultiplier.lean#L16-L19

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelLevelMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.Qx1

theorem Formalism.FourierDecayAlt.P.Qx1.model_level_lowering (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.l0 Y = M.l0A P Y := by sorry
