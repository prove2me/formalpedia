-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mono_le_iff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mono_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:57.498805+00:00
-- url     : https://prove2.me/theorems/8a95f837-7fd9-419a-8816-395121a01090
-- title:
--   leading Term Lemmas: mono le iff
-- statement:
--   The leading Term Lemmas construction uses the mono le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L511-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L511-L533

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mono_le_iff (f : Fin C → ℕ) (hf : Monotone f) (v : ℕ) (c : Fin C) :
    f c ≤ v ↔ c.val < ∑ w ∈ Finset.range (v + 1), (univ.filter fun c => f c = w).card := by sorry
