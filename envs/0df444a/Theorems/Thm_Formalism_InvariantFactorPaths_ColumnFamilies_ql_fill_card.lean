-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_fill_card
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_fill_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:51.107175+00:00
-- url     : https://prove2.me/theorems/1daae12b-0a3c-4746-bc97-befc30e9596c
-- title:
--   Column Families: ql fill card
-- statement:
--   The Column Families construction uses the ql fill card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L46-L55

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_fill_card {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (f : Fin N → Finset (Fin n)) (hf : ∀ j : Fin N, (f j).card = colH mu (lo + 1 + (j : ℕ))) (c : ℤ) :
    (ql_fill lo N f c).card = colH mu c := by sorry
