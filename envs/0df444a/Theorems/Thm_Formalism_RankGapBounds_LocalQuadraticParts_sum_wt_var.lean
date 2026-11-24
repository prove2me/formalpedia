-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_sum_wt_var
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.sum_wt_var
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:46.721415+00:00
-- url     : https://prove2.me/theorems/e312e883-a90c-4469-bee8-02dcb993a20a
-- title:
--   Local Quadratic Parts: sum wt var
-- statement:
--   The Local Quadratic Parts construction uses the sum wt var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L18-L34

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.sum_wt_var {α : Type*} [Fintype α] (δ : ℝ) :
    ∑ T : Finset α, wt δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by sorry
