-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_sq
-- name    : Formalism.FourierDecayAlt.P.LevelGrowthBounds.Pp_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:26.708615+00:00
-- url     : https://prove2.me/theorems/912fb699-9bbe-4b2b-a8cb-e386b808755d
-- title:
--   Level Growth Bounds: Pp sq
-- statement:
--   The Level Growth Bounds construction uses the Pp sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L62-L68

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

theorem Formalism.FourierDecayAlt.P.LevelGrowthBounds.Pp_sq {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) :
    Pp e i ^ 2 = ∏ l ∈ Icc 1 i, (1 + e l) := by sorry
