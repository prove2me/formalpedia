-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_lower_card
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.lower_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:30.01536+00:00
-- url     : https://prove2.me/theorems/eec00b3a-af45-4c95-ba55-96d4d8471ce9
-- title:
--   leading Term Lemmas: lower card
-- statement:
--   The leading Term Lemmas construction uses the lower card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L492-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L492-L509

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n C : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.lower_card (S : Finset (Fin C)) (hS : ∀ c ∈ S, ∀ c' ≤ c, c' ∈ S) (c : Fin C) :
    c ∈ S ↔ c.val < S.card := by sorry
