-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_conj_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.conj_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:34.372901+00:00
-- url     : https://prove2.me/theorems/8c53d26e-b94f-4f8a-af14-96e579783c16
-- title:
--   Unit Conjugation: conj iff
-- statement:
--   The Unit Conjugation construction uses the conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L85-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L85-L113

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
variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.conj_iff (hq : 0 < q) (hd : 0 < d) (h : IsLayer n q d ζ a b) (φ : L →+* ℂ)
    (σ : Gal(L/ℚ)) :
    (∀ x : L, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n := by sorry
