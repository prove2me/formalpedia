-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_pow_bound
-- name    : Formalism.FourierDecayAlt.P.LevelGrowthBounds.pow_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:37.203463+00:00
-- url     : https://prove2.me/theorems/ef6dcc02-81d6-47ec-bd28-d4b65490a1c2
-- title:
--   Level Growth Bounds: pow bound
-- statement:
--   The Level Growth Bounds construction uses the pow bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L116-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L116-L132

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LevelGrowthBounds
open Finset Real

theorem Formalism.FourierDecayAlt.P.LevelGrowthBounds.pow_bound (r : ℕ) (η : ℝ) (hη : 0 ≤ η) (hx : ((r:ℝ) + 1) * η ≤ 1 / 2) :
    ((1 + η) ^ (r+1)) ^ 2 ≤ 1 + 4 * ((r:ℝ) + 1) * η := by sorry
