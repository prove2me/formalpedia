-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_sep_other_zero
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.sep_other_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:53:01.168234+00:00
-- url     : https://prove2.me/theorems/aadaae6c-d652-4b01-8ac4-df3e53855fa9
-- title:
--   flip Two Three: sep other zero
-- statement:
--   The flip Two Three construction uses the sep other zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L120-L129

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.sep_other_zero {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu nu' : Fin n → ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = B0 lam nu) (hne : nu' ≠ nu) :
    sep lam nu nu' = 0 := by sorry
