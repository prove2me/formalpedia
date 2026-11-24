-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_autToPow_eq_neg_one_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.autToPow_eq_neg_one_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:21.821602+00:00
-- url     : https://prove2.me/theorems/926030c5-aed4-4896-b011-d01080e52336
-- title:
--   Unit Conjugation: aut To Pow eq neg one iff
-- statement:
--   The Unit Conjugation construction uses the aut To Pow eq neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L71-L74

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

theorem Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.autToPow_eq_neg_one_iff (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    hζ.autToPow ℚ σ = -1 ↔ σ ζ = ζ⁻¹ := by sorry
