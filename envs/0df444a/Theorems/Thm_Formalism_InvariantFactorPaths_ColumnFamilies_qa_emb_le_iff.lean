-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_emb_le_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_emb_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:46.656799+00:00
-- url     : https://prove2.me/theorems/a34d6204-96a6-4dce-9e08-26fe18b5ae89
-- title:
--   Column Families: qa emb le iff
-- statement:
--   The Column Families construction uses the qa emb le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L30-L38

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_emb_le_iff {n h : ℕ} (J : Finset (Fin n)) (hJ : J.card = h) (p : Fin h) (a : Fin n) :
    J.orderEmbOfFin hJ p ≤ a ↔ p.val < (J.filter (· ≤ a)).card := by sorry
