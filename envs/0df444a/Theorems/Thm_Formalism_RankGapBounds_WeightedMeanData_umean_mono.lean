-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_mono
-- name    : Formalism.RankGapBounds.WeightedMeanData.umean_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:05.419816+00:00
-- url     : https://prove2.me/theorems/ff5135c6-08fc-4be3-bb89-8c9b62067f68
-- title:
--   Weighted Mean Data: umean mono
-- statement:
--   The Weighted Mean Data construction uses the umean mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L48-L52

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

theorem Formalism.RankGapBounds.WeightedMeanData.umean_mono {X Y : ι → ℝ} (h : ∀ i, X i ≤ Y i) : umean X ≤ umean Y := by sorry
