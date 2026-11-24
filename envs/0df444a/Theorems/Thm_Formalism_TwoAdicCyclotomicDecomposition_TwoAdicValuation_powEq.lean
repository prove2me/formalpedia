-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_powEq
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.powEq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:04.067056+00:00
-- url     : https://prove2.me/theorems/73416c94-55ed-4b20-a63c-f90b6f0ac60b
-- title:
--   Two Adic Valuation: pow Eq
-- statement:
--   The Two Adic Valuation construction uses the pow Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L72-L80

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
open Formalism Formalism.TwoAdicCyclotomicDecomposition Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.powEq (N m : ℕ) (a : ℤ) (hz : a ^ m - 1 ≠ 0) :
    (a : ZMod (2 ^ N)) ^ m = 1 ↔ N ≤ padicValInt 2 (a ^ m - 1) := by sorry
