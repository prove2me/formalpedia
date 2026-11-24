-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_col_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_col_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:16.293919+00:00
-- url     : https://prove2.me/theorems/e726f2a6-1ed9-4c56-b771-803d3b1a90c9
-- title:
--   Column Families: qb col eq
-- statement:
--   The Column Families construction uses the qb col eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L97-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L97-L121

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_col_eq (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c)
    (h : ∀ a : Fin n, ((univ.filter (· ≤ a)).filter (· ∈ J)).card =
      ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card) : J = (canT mu c).1 := by sorry
