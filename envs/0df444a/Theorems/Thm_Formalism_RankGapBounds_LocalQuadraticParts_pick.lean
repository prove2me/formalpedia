-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pick
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.pick
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:48.466801+00:00
-- url     : https://prove2.me/theorems/bc9e08a0-a98f-4347-8a87-7730248e1ff2
-- title:
--   Local Quadratic Parts: pick
-- statement:
--   The Local Quadratic Parts construction uses the pick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L74-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L74-L122

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.pick {γ : Type*} (s : Finset γ) (w V X : γ → ℝ) (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hw : ∀ T ∈ s, 0 ≤ w T) (hsum : ∑ T ∈ s, w T = 1) (hV0 : ∀ T ∈ s, 0 ≤ V T)
    (hV : ∑ T ∈ s, w T * V T ≤ 2 / 3 * r) (hX0 : ∀ T ∈ s, 0 ≤ X T)
    (hXs : ∑ T ∈ s, w T * X T ≤ M) :
    ∃ T ∈ s, V T < r ∧ X T ≤ 4 * M := by sorry
