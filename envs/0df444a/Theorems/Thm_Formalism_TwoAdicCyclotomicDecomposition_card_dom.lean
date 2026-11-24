-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_dom
-- name    : Formalism.TwoAdicCyclotomicDecomposition.card_dom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:59:41.764558+00:00
-- url     : https://prove2.me/theorems/fc257f4d-be1a-406f-8ae4-641a55e53500
-- title:
--   Two Adic Cyclotomic Decomposition: card dom
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the card dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L259-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L259-L262

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.card_dom (s m : ℕ) :
    Nat.card (ℤˣ × Multiplicative (ZMod (2 ^ (m - s)))) = 2 ^ (m - s + 1) := by sorry
