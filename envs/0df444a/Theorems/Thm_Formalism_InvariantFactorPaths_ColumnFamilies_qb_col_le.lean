-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_col_le
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_col_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:42.259811+00:00
-- url     : https://prove2.me/theorems/61d93f73-c402-4932-9ed4-ba78315cd8a1
-- title:
--   Column Families: qb col le
-- statement:
--   The Column Families construction uses the qb col le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L81-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L81-L95

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_col_le (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c) (a : Fin n) :
    ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card := by sorry
