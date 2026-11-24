-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_detU_coe
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_detU_coe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:59.624907+00:00
-- url     : https://prove2.me/theorems/2a6ed5e4-1aef-4c6e-b0b9-5049a3b09be6
-- title:
--   Column Families: qc det U coe
-- statement:
--   The Column Families construction uses the qc det U coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L143-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L143-L143

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_detU_coe (n : ℕ) : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ _ (genMat ℤ n).det := by sorry
