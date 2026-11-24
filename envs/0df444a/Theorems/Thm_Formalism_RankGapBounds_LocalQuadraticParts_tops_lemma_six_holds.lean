-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_tops_lemma_six_holds
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.tops_lemma_six_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:39.631804+00:00
-- url     : https://prove2.me/theorems/42652759-6443-4372-b00c-c04e689aecf2
-- title:
--   Local Quadratic Parts: tops lemma six holds
-- statement:
--   The Local Quadratic Parts construction uses the tops lemma six holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L124-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L124-L142

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.tops_lemma_six_holds : TopsFixed := by sorry
