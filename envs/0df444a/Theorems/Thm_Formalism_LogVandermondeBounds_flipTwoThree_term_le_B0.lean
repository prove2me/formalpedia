-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_term_le_B0
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.term_le_B0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:54.907794+00:00
-- url     : https://prove2.me/theorems/e6fe45e0-a542-44e7-b2be-811734d5a4c8
-- title:
--   flip Two Three: term le B0
-- statement:
--   The flip Two Three construction uses the term le B0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L7-L11

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset

theorem Formalism.LogVandermondeBounds.flipTwoThree.term_le_B0 {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) : nu i - lam i.succ ≤ B0 lam nu := by sorry
