-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_zero
-- name    : Formalism.FourierDecayAlt.P.Mx2.multiplierPair_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:21.4959+00:00
-- url     : https://prove2.me/theorems/d1adf8c5-05c7-4370-ad78-d98a0f94a87c
-- title:
--   Mx2: multiplier Pair zero
-- statement:
--   The Mx2 construction uses the multiplier Pair zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L225-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelNablaStarRelations.lean#L225-L229

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

theorem Formalism.FourierDecayAlt.P.Mx2.multiplierPair_zero : (fnP 0 0 : Pr r) = 0 := by sorry
