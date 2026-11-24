-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_minor_ext
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_minor_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:30.012382+00:00
-- url     : https://prove2.me/theorems/e3479f55-852f-497b-b47d-73ba1fa59064
-- title:
--   Column Families: qr minor ext
-- statement:
--   The Column Families construction uses the qr minor ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L132-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L132-L158

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
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
variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_minor_ext (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K' S : Finset (Fin m)) {k k' : ℕ}
    (hK' : K'.card = k') (hS' : S.card = k') (hK : (qr_ext e K').card = k) (hS : (qr_ext e S).card = k) :
    (h.val.submatrix ((qr_ext e K').orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det =
      (if e then (t : R) else 1) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by sorry
