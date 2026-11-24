-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_E_fill
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_E_fill
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:53.2588+00:00
-- url     : https://prove2.me/theorems/0deb9d5b-3ec2-417a-8aa4-5eec038793ad
-- title:
--   Column Families: ql E fill
-- statement:
--   The Column Families construction uses the ql E fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L28-L36

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_E_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ql_E lo N (ql_fill lo N f) = f := by sorry
