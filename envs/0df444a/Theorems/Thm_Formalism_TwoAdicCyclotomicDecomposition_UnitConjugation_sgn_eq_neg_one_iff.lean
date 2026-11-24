-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_sgn_eq_neg_one_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.sgn_eq_neg_one_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:41.234822+00:00
-- url     : https://prove2.me/theorems/076a14da-e2c0-4ff4-a413-dd09dd7aae50
-- title:
--   Unit Conjugation: sgn eq neg one iff
-- statement:
--   The Unit Conjugation construction uses the sgn eq neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L51-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/ConjEqInvOfPowEqOne.lean#L51-L69

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

theorem Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.sgn_eq_neg_one_iff (hq : 0 < q) (ha : a ^ 2 = -(q : L)) (σ : Gal(L/ℚ)) :
    sgn σ a = -1 ↔ σ a = -a := by sorry
