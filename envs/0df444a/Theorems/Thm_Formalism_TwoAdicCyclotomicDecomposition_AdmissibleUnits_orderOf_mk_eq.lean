-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_orderOf_mk_eq
-- name    : Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.orderOf_mk_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:29:27.333901+00:00
-- url     : https://prove2.me/theorems/8e9e2a5c-b8d5-49c2-b80c-5910f2a33cc3
-- title:
--   Admissible Units: order Of mk eq
-- statement:
--   The Admissible Units construction uses the order Of mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L178-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L178-L189

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

theorem Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.orderOf_mk_eq {G : Type*} [CommGroup G] [Finite G] {x g : G} (hg : g ^ 2 = 1)
    (hx : g ∉ Subgroup.zpowers x) :
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = orderOf x := by sorry
