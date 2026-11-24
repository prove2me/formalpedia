-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_core
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:15.931986+00:00
-- url     : https://prove2.me/theorems/4df6892f-4446-42cd-b8ad-bc3ea2a2875a
-- title:
--   Column Families: ql core
-- statement:
--   The Column Families construction uses the ql core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L41-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L41-L84

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_core (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) {lo : ℤ} {N : ℕ}
    (m1 : lo ≤ mu (lastIdx n)) (m2 : mu 0 ≤ lo + N) (n1 : lo ≤ nu (lastIdx n)) (n2 : nu 0 ≤ lo + N)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 (ql_E lo N (qs_ext nu I)) : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_P ℤ (ql_E lo N (qs_ext mu K)) L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) *
        TMat nu I' I := by sorry
