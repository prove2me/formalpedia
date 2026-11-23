-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_growth
-- name    : Formalism.FourierDecayAlt.P.LevelGrowthBounds.growth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:19.008296+00:00
-- url     : https://prove2.me/theorems/00bf332f-a43a-4b02-b40b-3d2763e2252b
-- title:
--   Level Growth Bounds: growth
-- statement:
--   The Level Growth Bounds construction uses the growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L70-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean#L70-L114

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

theorem Formalism.FourierDecayAlt.P.LevelGrowthBounds.growth (r : ℕ) (ε δ : ℝ) (e a : ℕ → ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2)
    (he : ∀ i, 0 ≤ e i) (ha : ∀ i, 0 ≤ a i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ √(1 + e i) * ((1 + ε) * a (i - 1) + ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s))) :
    ∀ i, i ≤ r + 1 → a i ≤ (1 + (ε + 2 * δ)) ^ i * Pp e i * a 0 := by sorry
