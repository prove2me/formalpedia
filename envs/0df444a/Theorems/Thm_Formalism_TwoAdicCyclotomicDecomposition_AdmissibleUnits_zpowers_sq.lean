-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_zpowers_sq
-- name    : Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.zpowers_sq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:29:30.155842+00:00
-- url     : https://prove2.me/theorems/a506c8e7-9c7e-4591-b7f9-c770e00c801d
-- title:
--   Admissible Units: zpowers sq
-- statement:
--   The Admissible Units construction uses the zpowers sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L169-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L169-L176

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

theorem Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.zpowers_sq {G : Type*} [Group G] [Finite G] {g y : G} (hg : g ^ 2 = 1)
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g := by sorry
