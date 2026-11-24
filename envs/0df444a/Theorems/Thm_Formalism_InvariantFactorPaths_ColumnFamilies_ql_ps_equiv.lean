-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_ps_equiv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_ps_equiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:31.047544+00:00
-- url     : https://prove2.me/theorems/47e9cb2f-af1d-4818-86f5-fbea283eed01
-- title:
--   Column Families: ql ps equiv
-- statement:
--   The Column Families construction uses the ql ps equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L92-L98

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_ps_equiv (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) * ((ql_ps b mu nu y I : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_ps b mu nu (K, L) I' : ℤ) : GLCoord ℤ n) * TMat nu I' I := by sorry
