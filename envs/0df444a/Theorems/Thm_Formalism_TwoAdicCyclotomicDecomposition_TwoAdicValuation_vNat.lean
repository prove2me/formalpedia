-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_vNat
-- name    : Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.vNat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:10.215871+00:00
-- url     : https://prove2.me/theorems/4d7f377c-9a21-445a-ad1c-0f8771651963
-- title:
--   Two Adic Valuation: v Nat
-- statement:
--   The Two Adic Valuation construction uses the v Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/TwoAdic.lean#L12-L15

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

theorem Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.vNat (e : ℕ) (he : e ≠ 0) : (padicValNat 2 e : ℕ∞) = emultiplicity (2 : ℤ) (e : ℤ) := by sorry
