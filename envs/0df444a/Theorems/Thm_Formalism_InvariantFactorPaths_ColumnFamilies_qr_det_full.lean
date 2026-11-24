-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_full
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_full
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:27.77007+00:00
-- url     : https://prove2.me/theorems/da0cd0b9-dabb-4352-a3e5-e8dc33678942
-- title:
--   Column Families: qr det full
-- statement:
--   The Column Families construction uses the qr det full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L9-L14

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_full {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = m)
    (S : Finset (Fin m)) (hS : S.card = k) :
    (A.submatrix (S.orderEmbOfFin hS) (S.orderEmbOfFin hS)).det = A.det := by sorry
