-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_mul
-- name    : Formalism.RankGapBounds.WeightedMeanData.umean_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:14.744884+00:00
-- url     : https://prove2.me/theorems/44cdb8c0-7cf6-48c3-a17e-37d115b1e876
-- title:
--   Weighted Mean Data: umean mul
-- statement:
--   The Weighted Mean Data construction uses the umean mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L57-L58

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

theorem Formalism.RankGapBounds.WeightedMeanData.umean_mul (c : ℝ) (X : ι → ℝ) : umean (fun i => c * X i) = c * umean X := by sorry
