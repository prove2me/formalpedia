-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mapCoord_brk
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_brk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:35.05625+00:00
-- url     : https://prove2.me/theorems/952b4e70-26a7-4513-a5ff-478703795b20
-- title:
--   Column Families: qh map Coord brk
-- statement:
--   The Column Families construction uses the qh map Coord brk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L109-L119

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_mapCoord_brk [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord R (brk mu I) = ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
      ∏ c : ↥(TCols mu), qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q) := by sorry
