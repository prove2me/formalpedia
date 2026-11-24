-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_sep_self_abs
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.sep_self_abs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:57.367582+00:00
-- url     : https://prove2.me/theorems/0771619a-0de6-4524-aa19-8d645b97b52c
-- title:
--   flip Two Three: sep self abs
-- statement:
--   The flip Two Three construction uses the sep self abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L100-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L100-L118

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.sep_self_abs {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    |sep lam nu nu| ≤ (lam 0 - lam (Fin.last n) + n + 1) ^
      (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) := by sorry
