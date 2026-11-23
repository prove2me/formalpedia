-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_genPt_val
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_genPt_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:23.455127+00:00
-- url     : https://prove2.me/theorems/c12497e1-b1c3-47fb-af94-8da628b68a18
-- title:
--   Column Families: qc gen Pt val
-- statement:
--   The Column Families construction uses the qc gen Pt val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L21-L22

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_genPt_val (F : Type) [CommRing F] (n : ℕ) (a b : Fin n) :
    (qc_genPt F n).val a b = algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n) (X (a, b)) := by sorry
