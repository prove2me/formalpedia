-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_twoAdicOrder
-- name    : Formalism.TwoAdicCyclotomicDecomposition.twoAdicOrder
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:52:12.026788+00:00
-- url     : https://prove2.me/theorems/bf1d68c2-f3fb-4aeb-897f-987b9962aa0d
-- title:
--   Two Adic Cyclotomic Decomposition: two Adic Order
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the two Adic Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L101-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L101-L128

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open TwoAdicValuation

theorem Formalism.TwoAdicCyclotomicDecomposition.twoAdicOrder : TwoAdicOrder := by sorry
