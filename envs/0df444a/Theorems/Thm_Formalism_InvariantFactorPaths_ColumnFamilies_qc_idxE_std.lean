-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_idxE_std
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_idxE_std
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:41.534793+00:00
-- url     : https://prove2.me/theorems/9d59743e-588f-4406-a70f-d34ca23dd8b4
-- title:
--   Column Families: qc idx E std
-- statement:
--   The Column Families construction uses the qc idx E std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L64-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L64-L84

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_idxE_std (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) : StdT I ↔ StdT (qc_idxE mu ε I) := by sorry
