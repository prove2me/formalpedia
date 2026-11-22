-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_neg_not_mem_five
-- name    : Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.neg_not_mem_five
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:32.019514+00:00
-- url     : https://prove2.me/theorems/e7f40455-65fd-45b0-b825-b8b1fbd6cc1a
-- title:
--   Admissible Units: neg not mem five
-- statement:
--   The Admissible Units construction uses the neg not mem five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L46-L53

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

theorem Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.neg_not_mem_five (n : ℕ) :
    (-1 : (ZMod (2 ^ (n + 2)))ˣ) ∉ Subgroup.zpowers (u5 (n + 2)) := by sorry
