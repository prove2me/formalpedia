-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_le_const
-- name    : Formalism.RankGapBounds.WeightedMeanData.wmean_le_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:09.535847+00:00
-- url     : https://prove2.me/theorems/7c9913c2-9959-4bab-8f6c-cf2cc257536b
-- title:
--   Weighted Mean Data: wmean le const
-- statement:
--   The Weighted Mean Data construction uses the wmean le const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L34-L38

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
variable {ι : Type} [Fintype ι]

theorem Formalism.RankGapBounds.WeightedMeanData.wmean_le_const [Nonempty ι] {d X : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ)
    (h : ∀ i, X i ≤ c) : wmean d X ≤ c := by sorry
