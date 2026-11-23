-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_card_sub
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_card_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:07.686564+00:00
-- url     : https://prove2.me/theorems/1decb8bb-5c14-4bdc-8957-7af2cfba39ed
-- title:
--   Column Families: qa card sub
-- statement:
--   The Column Families construction uses the qa card sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L133-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L133-L143

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_card_sub {T : Finset ℤ} (P : ↥T → Prop) [DecidablePred P]
    [DecidablePred fun d => ∃ h : d ∈ T, P ⟨d, h⟩] :
    (univ.filter P).card = (T.filter fun d => ∃ h : d ∈ T, P ⟨d, h⟩).card := by sorry
