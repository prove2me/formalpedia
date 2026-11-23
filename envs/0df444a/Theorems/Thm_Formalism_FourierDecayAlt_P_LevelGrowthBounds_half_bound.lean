-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_half_bound
-- name    : Formalism.FourierDecayAlt.P.LevelGrowthBounds.half_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:15.476265+00:00
-- url     : https://prove2.me/theorems/56fa2aa9-0519-4039-95c5-7a4ea2a1a4a4
-- title:
--   Level Growth Bounds: half bound
-- statement:
--   The Level Growth Bounds construction uses the half bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L134-L139

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

theorem Formalism.FourierDecayAlt.P.LevelGrowthBounds.half_bound (r : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) (hr : (r:ℝ) * (12 * u) ≤ 1) :
    ((r:ℝ) + 1) * (3 * u) ≤ 1 / 2 := by sorry
