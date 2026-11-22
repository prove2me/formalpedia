-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_lt_colH_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_lt_colH_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:06.545538+00:00
-- url     : https://prove2.me/theorems/0e3957f9-274a-4ca7-9576-a88a0c42430c
-- title:
--   Column Families: qb lt col H iff
-- statement:
--   The Column Families construction uses the qb lt col H iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L123-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L123-L143

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (b : Fin n) :
    b.val < colH mu c ↔ c ≤ mu b := by sorry
