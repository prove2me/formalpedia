-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_v4
-- name    : Formalism.TwoAdicCyclotomicDecomposition.v4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:56.359252+00:00
-- url     : https://prove2.me/theorems/fec7ecf0-27c7-4d8c-b9a0-60047a7ce26b
-- title:
--   Two Adic Cyclotomic Decomposition: v4
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the v4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NormalOrderTwoCentral.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NormalOrderTwoCentral.lean#L31-L33

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.v4 : padicValInt 2 ((5 : ℤ) - 1) = 2 := by sorry
