-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_mn_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:39.188965+00:00
-- url     : https://prove2.me/theorems/b1c1d8d8-a4e1-49af-821a-7964d18ba7f6
-- title:
--   Column Families: qs mn eq
-- statement:
--   The Column Families construction uses the qs mn eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L19-L21

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_mn_eq {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    qs_mn g J I = Matrix.det (Matrix.of fun a b : Fin h => g (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by sorry
