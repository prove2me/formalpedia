-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_sum_aT_mul
-- name    : Formalism.RankGapBounds.WeightedMeanData.Data.sum_aT_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:30.392844+00:00
-- url     : https://prove2.me/theorems/d740affd-919d-41e5-ab89-0743cb863fd5
-- title:
--   Data: sum a T mul
-- statement:
--   The Data construction uses the sum a T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L156-L157

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

theorem Formalism.RankGapBounds.WeightedMeanData.Data.sum_aT_mul (g : ℝ) : ∑ t, D.aT t * g = D.sumA * g := by sorry
