-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_add
-- name    : Formalism.RankGapBounds.WeightedMeanData.wmean_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:09.100187+00:00
-- url     : https://prove2.me/theorems/e9c4a5c6-8166-4084-9d34-c080583e182c
-- title:
--   Weighted Mean Data: wmean add
-- statement:
--   The Weighted Mean Data construction uses the wmean add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L24-L25

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

theorem Formalism.RankGapBounds.WeightedMeanData.wmean_add (d X Y : ι → ℝ) : wmean d (fun i => X i + Y i) = wmean d X + wmean d Y := by sorry
