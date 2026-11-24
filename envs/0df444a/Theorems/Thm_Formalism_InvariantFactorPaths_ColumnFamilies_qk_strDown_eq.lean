-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_strDown_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_strDown_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:38.591886+00:00
-- url     : https://prove2.me/theorems/f5c2b714-1144-4a2d-bfe5-b0103e202508
-- title:
--   Column Families: qk str Down eq
-- statement:
--   The Column Families construction uses the qk str Down eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntSym.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntSym.lean#L41-L44

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_strDown_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strDown mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown mu b := by sorry
