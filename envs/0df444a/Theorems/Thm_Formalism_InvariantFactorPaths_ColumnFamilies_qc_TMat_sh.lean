-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_TMat_sh
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_TMat_sh
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:14.047899+00:00
-- url     : https://prove2.me/theorems/57352306-29ec-4cb9-940b-9e42394b713d
-- title:
--   Column Families: qc TMat sh
-- statement:
--   The Column Families construction uses the qc TMat sh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean#L93-L102

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_TMat_sh (mu : Fin n → ℤ) (ε : ℤ) (J I : TIdx (qc_sh mu ε)) :
    TMat (qc_sh mu ε) J I =
      ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * TMat mu (qc_idxE mu ε J) (qc_idxE mu ε I) := by sorry
