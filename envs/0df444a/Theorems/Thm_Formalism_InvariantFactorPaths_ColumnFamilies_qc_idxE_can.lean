-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_idxE_can
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_idxE_can
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:27.432798+00:00
-- url     : https://prove2.me/theorems/c15caa33-da14-4ca9-95b0-80775e4e8b9d
-- title:
--   Column Families: qc idx E can
-- statement:
--   The Column Families construction uses the qc idx E can property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L54-L57

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_idxE_can (mu : Fin n → ℤ) (ε : ℤ) : qc_idxE mu ε (canT (qc_sh mu ε)) = canT mu := by sorry
