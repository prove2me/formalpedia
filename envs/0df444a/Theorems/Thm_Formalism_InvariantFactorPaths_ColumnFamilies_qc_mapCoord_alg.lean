-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_mapCoord_alg
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_mapCoord_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:07.222092+00:00
-- url     : https://prove2.me/theorems/46d5aa48-1e48-4460-91cd-7fe4e488f9e4
-- title:
--   Column Families: qc map Coord alg
-- statement:
--   The Column Families construction uses the qc map Coord alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L24-L27

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_mapCoord_alg {n : ℕ} (F : Type) [CommRing F] (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) P) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) P) := by sorry
