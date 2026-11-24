-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_can
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_mem_can
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.025069+00:00
-- url     : https://prove2.me/theorems/0b4c110e-dfed-4b16-a176-7d35c4fad2ef
-- title:
--   Column Families: ql mem can
-- statement:
--   The Column Families construction uses the ql mem can property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L88-L90

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_mem_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (a : Fin n) :
    a ∈ qs_ext mu (canT mu) c ↔ c ≤ mu a := by sorry
