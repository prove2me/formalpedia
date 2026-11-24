-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_map
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:05.948401+00:00
-- url     : https://prove2.me/theorems/2824e227-11f4-4f1d-adef-27bab4a38811
-- title:
--   Column Families: qc ev GL map
-- statement:
--   The Column Families construction uses the qc ev GL map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L49-L55

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_map {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (g : GL (Fin n) R) :
    evGL (Matrix.GeneralLinearGroup.map φ g) = φ.comp (evGL g) := by sorry
