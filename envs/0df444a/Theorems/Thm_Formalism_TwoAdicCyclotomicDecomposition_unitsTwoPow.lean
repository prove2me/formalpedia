-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_unitsTwoPow
-- name    : Formalism.TwoAdicCyclotomicDecomposition.unitsTwoPow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:46.724928+00:00
-- url     : https://prove2.me/theorems/732ee176-369d-4311-8b15-1aefb3e5117f
-- title:
--   Two Adic Cyclotomic Decomposition: units Two Pow
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the units Two Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L206-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean#L206-L218

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
open AdmissibleUnits

theorem Formalism.TwoAdicCyclotomicDecomposition.unitsTwoPow : UnitsTwoPow := by sorry
