-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_wt_nonneg
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.wt_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:42.104015+00:00
-- url     : https://prove2.me/theorems/47996dc4-1c4b-4ccd-abf8-a6c179539ce7
-- title:
--   Local Quadratic Parts: wt nonneg
-- statement:
--   The Local Quadratic Parts construction uses the wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L7-L9

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RandomSubsetLemmaCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset

theorem Formalism.RankGapBounds.LocalQuadraticParts.wt_nonneg {α : Type*} [Fintype α] {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt δ T := by sorry
