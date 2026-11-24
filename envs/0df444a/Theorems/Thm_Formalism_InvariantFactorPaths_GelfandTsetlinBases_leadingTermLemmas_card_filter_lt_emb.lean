-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_card_filter_lt_emb
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.card_filter_lt_emb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:54.626289+00:00
-- url     : https://prove2.me/theorems/6dcd079c-db0d-4e76-8d5b-87f3142ce46c
-- title:
--   leading Term Lemmas: card filter lt emb
-- statement:
--   The leading Term Lemmas construction uses the card filter lt emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L398-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean#L398-L400

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.card_filter_lt_emb (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (i : Fin k) :
    (J.filter (· < J.orderEmbOfFin h i)).card = i.val := by sorry
