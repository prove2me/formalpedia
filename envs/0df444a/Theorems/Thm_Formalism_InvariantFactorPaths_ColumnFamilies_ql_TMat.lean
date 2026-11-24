-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_TMat
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_TMat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:43.629718+00:00
-- url     : https://prove2.me/theorems/9425a8b9-2fd4-4c36-8052-89d30863bfdf
-- title:
--   Column Families: ql TMat
-- statement:
--   The Column Families construction uses the ql TMat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L82-L86

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_TMat {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (J I : TIdx mu) :
    TMat mu J I = ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext mu J) j) (ql_E lo N (qs_ext mu I) j) := by sorry
