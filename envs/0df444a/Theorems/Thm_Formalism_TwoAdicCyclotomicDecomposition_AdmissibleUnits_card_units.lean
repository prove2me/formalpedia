-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_card_units
-- name    : Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.card_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:14.340576+00:00
-- url     : https://prove2.me/theorems/5dd711a8-76e0-4ceb-9009-7e8fc5b3fbd9
-- title:
--   Admissible Units: card units
-- statement:
--   The Admissible Units construction uses the card units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L69-L72

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

theorem Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.card_units (n : ℕ) : Nat.card (ZMod (2 ^ (n + 1)))ˣ = 2 ^ n := by sorry
