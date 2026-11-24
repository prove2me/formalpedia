-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_sum_wt_bad
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.sum_wt_bad
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:25:43.461427+00:00
-- url     : https://prove2.me/theorems/3b26399a-ba62-4649-8a75-7801812f7c6f
-- title:
--   Local Quadratic Parts: sum wt bad
-- statement:
--   The Local Quadratic Parts construction uses the sum wt bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L36-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/RandomSubsetLemmaCounterexample.lean#L36-L72

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.sum_wt_bad {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)] (hω : ∀ p, 0 ≤ ω p)
    (hBAD : ∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
      wt δ T ≤ β * δ) :
    ∑ T : Finset α, wt δ T * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤
      β * δ * Fintype.card α * ∑ p, ω p := by sorry
