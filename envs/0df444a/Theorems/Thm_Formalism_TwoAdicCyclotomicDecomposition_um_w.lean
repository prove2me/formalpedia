-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_um_w
-- name    : Formalism.TwoAdicCyclotomicDecomposition.um_w
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:59:58.617249+00:00
-- url     : https://prove2.me/theorems/23433b42-4d64-4c69-bf51-3f3a4e2f8675
-- title:
--   Two Adic Cyclotomic Decomposition: um w
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the um w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L217-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/NegOneNeOneUnitsZmodFour.lean#L217-L221

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

theorem Formalism.TwoAdicCyclotomicDecomposition.um_w {s m : ℕ} (h : s ≤ m) :
    ZMod.unitsMap (pow_dvd_pow 2 (by omega : s + 2 ≤ m + 2)) (wgen s m) = 1 := by sorry
