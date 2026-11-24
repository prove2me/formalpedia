-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_val_odd
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.val_odd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:19.39969+00:00
-- url     : https://prove2.me/theorems/357667a5-7f05-4497-b5d4-7b21269429e8
-- title:
--   Two Adic Valuation: val odd
-- statement:
--   The Two Adic Valuation construction uses the val odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L59-L70

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

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.val_odd (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (hod : Odd e) :
    padicValInt 2 (a ^ e - 1) = padicValInt 2 (a - 1) := by sorry
