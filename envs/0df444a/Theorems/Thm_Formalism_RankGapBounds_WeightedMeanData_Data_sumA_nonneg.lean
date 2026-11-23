-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_sumA_nonneg
-- name    : Formalism.RankGapBounds.WeightedMeanData.Data.sumA_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:54.702584+00:00
-- url     : https://prove2.me/theorems/7931182b-dc49-4e6c-bdee-c8326bdc0c4a
-- title:
--   Data: sum A nonneg
-- statement:
--   The Data construction uses the sum A nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L152-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L152-L154

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
open Formalism.RankGapBounds.WeightedMeanData.Data
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

theorem Formalism.RankGapBounds.WeightedMeanData.Data.sumA_nonneg (hS : D.HidaSetting C) : 0 ≤ D.sumA := by sorry
