-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_sum_indices_eq_sum_columns
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.sum_indices_eq_sum_columns
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:50.38175+00:00
-- url     : https://prove2.me/theorems/67976905-c931-45b1-91ed-87fa04fe41f3
-- title:
--   Column Families: sum indices eq sum columns
-- statement:
--   The Column Families construction uses the sum indices eq sum columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L60-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L60-L80

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.sum_indices_eq_sum_columns {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ}
    (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ lo + N) (φ : (Fin N → Finset (Fin n)) → M)
    (hφ : ∀ f, (∃ j : Fin N, (f j).card ≠ colH mu (lo + 1 + (j : ℕ))) → φ f = 0) :
    ∑ I : TIdx mu, φ (ql_E lo N (qs_ext mu I)) = ∑ f, φ f := by sorry
