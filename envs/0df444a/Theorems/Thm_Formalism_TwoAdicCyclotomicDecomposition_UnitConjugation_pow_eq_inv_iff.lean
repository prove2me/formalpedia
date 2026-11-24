-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_pow_eq_inv_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.pow_eq_inv_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:56.870664+00:00
-- url     : https://prove2.me/theorems/18ec4175-2241-4b17-ab39-f1254acaf2dd
-- title:
--   Unit Conjugation: pow eq inv iff
-- statement:
--   The Unit Conjugation construction uses the pow eq inv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L18-L25

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation

theorem Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.pow_eq_inv_iff {K : Type*} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (k : ℕ) : ζ ^ k = ζ⁻¹ ↔ (k : ZMod m) = -1 := by sorry
