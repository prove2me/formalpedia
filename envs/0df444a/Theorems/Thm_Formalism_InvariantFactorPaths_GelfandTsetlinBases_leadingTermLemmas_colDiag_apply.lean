-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_colDiag_apply
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.colDiag_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:15.768812+00:00
-- url     : https://prove2.me/theorems/95250049-74be-452e-a046-70c82db5651e
-- title:
--   leading Term Lemmas: col Diag apply
-- statement:
--   The leading Term Lemmas construction uses the col Diag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L416-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L416-L446

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
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.colDiag_apply (J : Finset (Fin n)) (a b : Fin n) :
    colDiag J (a, b) = if nthElt J a.val = b.val then 1 else 0 := by sorry
