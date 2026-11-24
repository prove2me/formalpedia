-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_y_sum
-- name    : Formalism.RankGapBounds.LocalQuadraticParts.pm_y_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:16.584724+00:00
-- url     : https://prove2.me/theorems/156b3677-be47-4f02-a3a2-d37a7d5fb56e
-- title:
--   Local Quadratic Parts: pm y sum
-- statement:
--   The Local Quadratic Parts construction uses the pm y sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L160-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/PmModulusFacts.lean#L160-L229

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

theorem Formalism.RankGapBounds.LocalQuadraticParts.pm_y_sum (M N : ℕ) (hM : 2 ≤ M) (Y : ℝ) (hY : 1 ≤ Y) (hNY : (N : ℝ) ≤ Y) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1))
    (hsY : ∀ l ∈ s, (l : ℝ) ≤ Y) :
    ∑ l ∈ s, Real.log l / (l : ℝ) ≤ 4 * Real.log Y * (1 + Real.log Y) / M := by sorry
