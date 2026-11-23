-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_snoc
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_snoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:18.224944+00:00
-- url     : https://prove2.me/theorems/b63c352c-832a-4e7e-86ca-44b6631f46f0
-- title:
--   Column Families: qr det snoc
-- statement:
--   The Column Families construction uses the qr det snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L107-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L107-L122

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_snoc (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).det =
      (t : R) * (g1.val.submatrix r c).det := by sorry
