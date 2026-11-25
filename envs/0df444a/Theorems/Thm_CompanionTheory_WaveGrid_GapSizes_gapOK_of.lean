-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_GapSizes_gapOK_of
-- name    : CompanionTheory.WaveGrid.GapSizes.gapOK_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:24.284962+00:00
-- url     : https://prove2.me/theorems/df64df55-747d-4703-9047-69ab523a7f85
-- title:
--   Gap Sizes: gap OK of
-- statement:
--   The Gap Sizes construction uses the gap OK of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/GapSizes.lean#L54-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/GapSizes.lean#L54-L121

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_GapSizes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.GapSizes

theorem CompanionTheory.WaveGrid.GapSizes.gapOK_of (k r : ℕ) (hk : 1 ≤ k) (Cg : ℝ) (hCg : 1000 ≤ Cg) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4) := by sorry
