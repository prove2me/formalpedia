-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_mulOp_mul
-- name    : Formalism.FourierDecayAlt.P.Mx2.mulOp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:17.858348+00:00
-- url     : https://prove2.me/theorems/c1a7b931-77d6-4a50-bebc-b118721549b4
-- title:
--   Mx2: mul Op mul
-- statement:
--   The Mx2 construction uses the mul Op mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L60-L61

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

theorem Formalism.FourierDecayAlt.P.Mx2.mulOp_mul (f g : Fn r) : mulOp f * mulOp g = mulOp (f * g) := by sorry
