-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_iota_neg
-- name    : Formalism.TwoAdicCyclotomicDecomposition.iota_neg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:53.612843+00:00
-- url     : https://prove2.me/theorems/738173e7-0387-4895-8c9b-e940a9c51f73
-- title:
--   Two Adic Cyclotomic Decomposition: iota neg
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the iota neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L201-L203

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.iota_neg (n : ℕ) : iota n (-1) = -1 := by sorry
