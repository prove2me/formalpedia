-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_genPt_int
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_genPt_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:34.57686+00:00
-- url     : https://prove2.me/theorems/87d6ed15-268b-42bc-83c3-8b9a830340f9
-- title:
--   Column Families: qc ev GL gen Pt int
-- statement:
--   The Column Families construction uses the qc ev GL gen Pt int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L43-L47

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_genPt_int (n : ℕ) : evGL (qc_genPt ℤ n) = RingHom.id _ := by sorry
