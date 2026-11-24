-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_sep_self_ne_zero
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.sep_self_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:59.756382+00:00
-- url     : https://prove2.me/theorems/02b7d486-f92d-494c-ae24-c38149cb7cd9
-- title:
--   flip Two Three: sep self ne zero
-- statement:
--   The flip Two Three construction uses the sep self ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L54-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L54-L74

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.sep_self_ne_zero {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    sep lam nu nu ≠ 0 := by sorry
