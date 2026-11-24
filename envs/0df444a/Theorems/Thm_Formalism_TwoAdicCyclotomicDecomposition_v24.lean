-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_v24
-- name    : Formalism.TwoAdicCyclotomicDecomposition.v24
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:10.28774+00:00
-- url     : https://prove2.me/theorems/adb72ef6-49d4-41e3-a974-bbb96ea7aeac
-- title:
--   Two Adic Cyclotomic Decomposition: v24
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the v24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NormalOrderTwoCentral.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NormalOrderTwoCentral.lean#L26-L29

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

theorem Formalism.TwoAdicCyclotomicDecomposition.v24 : padicValInt 2 ((5 : ℤ) ^ 2 - 1) = 3 := by sorry
