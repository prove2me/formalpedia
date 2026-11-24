-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_card_erase_Iset
-- name    : Formalism.LogVandermondeBounds.flipTwoThree.card_erase_Iset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:25.111818+00:00
-- url     : https://prove2.me/theorems/0490bdad-7e95-47f3-8670-b5891e6616ff
-- title:
--   flip Two Three: card erase Iset
-- statement:
--   The flip Two Three construction uses the card erase Iset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/InterlacingSeparation.lean#L76-L83

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

theorem Formalism.LogVandermondeBounds.flipTwoThree.card_erase_Iset {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) :
    ((Iset lam (B0 lam nu) i).erase (nu i)).card = (min (len lam i) (B0 lam nu)).toNat := by sorry
