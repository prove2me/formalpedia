-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_mk_comm
-- name    : Formalism.FourierDecayAlt.P.Mx2.mk_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:00.741144+00:00
-- url     : https://prove2.me/theorems/b136d8bd-44eb-4748-ab26-3342bb851b86
-- title:
--   Mx2: mk comm
-- statement:
--   The Mx2 construction uses the mk comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L303-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L303-L306

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx2.mk_comm (X Xs Y Ys : Op r) (h1 : X * Y = Y * X) (h2 : Xs * Ys = Ys * Xs) : mk X Xs * mk Y Ys = mk Y Ys * mk X Xs := by sorry
