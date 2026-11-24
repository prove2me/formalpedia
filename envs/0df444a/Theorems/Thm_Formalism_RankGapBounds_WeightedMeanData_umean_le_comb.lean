-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_le_comb
-- name    : Formalism.RankGapBounds.WeightedMeanData.umean_le_comb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:57.103225+00:00
-- url     : https://prove2.me/theorems/925227ec-1be0-424e-8e5b-b8a1a22c788b
-- title:
--   Weighted Mean Data: umean le comb
-- statement:
--   The Weighted Mean Data construction uses the umean le comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L66-L77

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

theorem Formalism.RankGapBounds.WeightedMeanData.umean_le_comb [Nonempty ι] {X A B P E : ι → ℝ} (p q K : ℝ)
    (h : ∀ i, X i ≤ A i + B i + p * P i + q * E i + K) :
    umean X ≤ umean A + umean B + p * umean P + q * umean E + K := by sorry
