-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_five_unit_coe_nat
-- name    : Formalism.TwoAdicCyclotomicDecomposition.five_unit_coe_nat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:11.038397+00:00
-- url     : https://prove2.me/theorems/52957910-ce69-4dec-90c6-f95da72fe0f3
-- title:
--   Two Adic Cyclotomic Decomposition: five unit coe nat
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the five unit coe nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L36-L36

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

theorem Formalism.TwoAdicCyclotomicDecomposition.five_unit_coe_nat (n : ℕ) : ((u5 n : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = ((5 : ℕ) : ZMod (2 ^ n)) := by sorry
