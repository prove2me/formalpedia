-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_nonneg
-- name    : Formalism.FourierDecayAlt.P.LevelGrowthBounds.Pp_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:54.015282+00:00
-- url     : https://prove2.me/theorems/ad4c23ed-6dde-435c-86a2-31d3ce59483a
-- title:
--   Level Growth Bounds: Pp nonneg
-- statement:
--   The Level Growth Bounds construction uses the Pp nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L53-L54

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

theorem Formalism.FourierDecayAlt.P.LevelGrowthBounds.Pp_nonneg {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) : 0 ≤ Pp e i := by sorry
