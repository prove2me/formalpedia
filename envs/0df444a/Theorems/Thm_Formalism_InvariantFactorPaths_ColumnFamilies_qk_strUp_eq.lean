-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_strUp_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_strUp_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:45.130865+00:00
-- url     : https://prove2.me/theorems/49d5c19d-caec-408f-aa5e-c7da3b4c46b4
-- title:
--   Column Families: qk str Up eq
-- statement:
--   The Column Families construction uses the qk str Up eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntSym.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntSym.lean#L36-L39

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_strUp_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strUp mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp mu b := by sorry
