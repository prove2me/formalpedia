-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mem_iff_nthElt
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mem_iff_nthElt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:42.883845+00:00
-- url     : https://prove2.me/theorems/b808f203-c829-4d34-be20-956dd8ea954e
-- title:
--   leading Term Lemmas: mem iff nth Elt
-- statement:
--   The leading Term Lemmas construction uses the mem iff nth Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L372-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L372-L387

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mem_iff_nthElt (J : Finset (Fin n)) (b : Fin n) : b ∈ J ↔ ∃ a : Fin n, nthElt J a.val = b.val := by sorry
