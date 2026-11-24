-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_E_card
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_E_card
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:51.402401+00:00
-- url     : https://prove2.me/theorems/e5b734f1-a103-47ae-ad89-34b08001f2f2
-- title:
--   Column Families: ql E card
-- statement:
--   The Column Families construction uses the ql E card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L57-L58

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_E_card {mu : Fin n → ℤ} (hmu : Dominant mu) (lo : ℤ) (N : ℕ) (I : TIdx mu) (j : Fin N) :
    (ql_E lo N (qs_ext mu I) j).card = colH mu (lo + 1 + (j : ℕ)) := by sorry
