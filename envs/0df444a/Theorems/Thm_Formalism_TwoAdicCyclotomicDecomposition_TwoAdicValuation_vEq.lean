-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_vEq
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.vEq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:07.934131+00:00
-- url     : https://prove2.me/theorems/f2bb27a1-8406-4de2-8115-19ed57557a1b
-- title:
--   Two Adic Valuation: v Eq
-- statement:
--   The Two Adic Valuation construction uses the v Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L6-L10

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

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.vEq (z : ℤ) (hz : z ≠ 0) : (padicValInt 2 z : ℕ∞) = emultiplicity (2 : ℤ) z := by sorry
