-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_sum_cover
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.pm_sum_cover
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:01.426191+00:00
-- url     : https://prove2.me/theorems/9b7e375e-08cf-48db-89fe-15fefe87404a
-- title:
--   Local Quadratic Parts: pm sum cover
-- statement:
--   The Local Quadratic Parts construction uses the pm sum cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L42-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L42-L71

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
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

theorem Formalism.RankGapBounds.LocalQuadraticParts.pm_sum_cover (f : ℕ → ℝ) (hf : ∀ l, 0 ≤ f l) (M N : ℕ) (hM : 2 ≤ M) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1)) :
    ∑ l ∈ s, f l ≤
      ∑ k ∈ range N, f ((k + 1) * M + 1) + ∑ k ∈ range N, f ((k + 1) * M - 1) := by sorry
