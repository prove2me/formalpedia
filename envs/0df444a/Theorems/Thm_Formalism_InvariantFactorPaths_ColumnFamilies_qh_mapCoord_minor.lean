-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mapCoord_minor
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_minor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:21.92908+00:00
-- url     : https://prove2.me/theorems/c80fde26-dc86-48fc-883f-7172dc58bd88
-- title:
--   Column Families: qh map Coord minor
-- statement:
--   The Column Families construction uses the qh map Coord minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L96-L107

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
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
variable {n : ℕ} {R : Type} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_minor [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (S : Finset (Fin n))
    (hS : S.card = colH mu c) :
    mapCoord R (minorC (canT mu c).1 S (canT mu c).2 hS) =
      qhN R (colH mu c) (colH_le mu c) (fun q => S.orderEmbOfFin hS q) := by sorry
