-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_galMap_eq_JJ_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.galMap_eq_JJ_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:44.539607+00:00
-- url     : https://prove2.me/theorems/b9c4296a-88ef-48fe-bff9-97c24b3a1a4f
-- title:
--   Unit Conjugation: gal Map eq JJ iff
-- statement:
--   The Unit Conjugation construction uses the gal Map eq JJ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L76-L78

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

theorem Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.galMap_eq_JJ_iff (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    galMap hζ a b σ = JJ n ↔ hζ.autToPow ℚ σ = -1 ∧ sgn σ a = -1 ∧ sgn σ b = -1 := by sorry
