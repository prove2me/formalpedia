-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_row_strictMono
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_row_strictMono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:15.309604+00:00
-- url     : https://prove2.me/theorems/22419829-c6f7-494f-9d0f-2ea570f9cd20
-- title:
--   Column Families: qa row strict Mono
-- statement:
--   The Column Families construction uses the qa row strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean#L16-L17

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_row_strictMono {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    StrictMono (qa_row I c) := by sorry
