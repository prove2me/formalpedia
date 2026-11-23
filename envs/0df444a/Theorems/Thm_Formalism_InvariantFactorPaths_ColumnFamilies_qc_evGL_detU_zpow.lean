-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_detU_zpow
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_detU_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:25.227163+00:00
-- url     : https://prove2.me/theorems/bc4d3799-324e-4c92-a953-4789d71759ea
-- title:
--   Column Families: qc ev GL det U zpow
-- statement:
--   The Column Families construction uses the qc ev GL det U zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L158-L161

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_detU_zpow {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) (m : ℤ) :
    evGL g ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qc_dU g ^ m : Rˣ) : R) := by sorry
