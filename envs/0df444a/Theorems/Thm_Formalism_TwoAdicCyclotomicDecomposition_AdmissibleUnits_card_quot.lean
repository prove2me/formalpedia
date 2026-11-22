-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_card_quot
-- name    : Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.card_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:09.389103+00:00
-- url     : https://prove2.me/theorems/87242dd7-f253-4737-8eab-0abb5ee45ddc
-- title:
--   Admissible Units: card quot
-- statement:
--   The Admissible Units construction uses the card quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L191-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L191-L201

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits

theorem Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.card_quot (n : ℕ) : Nat.card ((ZMod (2 ^ (n + 2)))ˣ ⧸
    Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) = 2 ^ n := by sorry
