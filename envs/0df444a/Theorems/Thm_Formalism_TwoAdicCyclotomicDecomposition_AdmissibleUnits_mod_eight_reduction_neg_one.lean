-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mod_eight_reduction_neg_one
-- name    : Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.mod_eight_reduction_neg_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:29:29.54203+00:00
-- url     : https://prove2.me/theorems/9b81cf8f-44f7-4f59-a527-06804a1f25f4
-- title:
--   Admissible Units: mod eight reduction neg one
-- statement:
--   The Admissible Units construction uses the mod eight reduction neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L31-L33

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

theorem Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.mod_eight_reduction_neg_one (N : ℕ) (h : 8 ∣ 2 ^ N) : r8 N h (-1) = -1 := by sorry
