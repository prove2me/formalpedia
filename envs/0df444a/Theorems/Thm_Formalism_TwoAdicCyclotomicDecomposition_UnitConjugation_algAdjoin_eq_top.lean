-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_algAdjoin_eq_top
-- name    : Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.algAdjoin_eq_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:38.062346+00:00
-- url     : https://prove2.me/theorems/16180478-ff2e-4bb5-a230-d47a7ce2d072
-- title:
--   Unit Conjugation: alg Adjoin eq top
-- statement:
--   The Unit Conjugation construction uses the alg Adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L80-L83

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

theorem Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.algAdjoin_eq_top (h : IsLayer n q d ζ a b) : Algebra.adjoin ℚ ({ζ, a, b} : Set L) = ⊤ := by sorry
