-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_conj_eq_inv_of_pow_eq_one
-- name    : Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.conj_eq_inv_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:34.94553+00:00
-- url     : https://prove2.me/theorems/82484f63-ed83-4efe-9dc4-47192922b4f2
-- title:
--   Unit Conjugation: conj eq inv of pow eq one
-- statement:
--   The Unit Conjugation construction uses the conj eq inv of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L12-L16

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

theorem Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.conj_eq_inv_of_pow_eq_one {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    starRingEnd ℂ z = z⁻¹ := by sorry
