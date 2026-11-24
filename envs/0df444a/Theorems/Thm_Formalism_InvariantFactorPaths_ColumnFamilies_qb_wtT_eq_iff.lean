-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_eq_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_wtT_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:54.701841+00:00
-- url     : https://prove2.me/theorems/bdd15456-aed1-4b59-b84e-2da3cc85a8b2
-- title:
--   Column Families: qb wt T eq iff
-- statement:
--   The Column Families construction uses the qb wt T eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L183-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreW.lean#L183-L204

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_wtT_eq_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : qb_wtT mu I = mu ↔ I = canT mu := by sorry
