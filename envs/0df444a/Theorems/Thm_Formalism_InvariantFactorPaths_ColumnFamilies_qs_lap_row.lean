-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_lap_row
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_lap_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:32.17588+00:00
-- url     : https://prove2.me/theorems/d380405c-d197-4223-a05d-9fe4a1a8b17c
-- title:
--   Column Families: qs lap row
-- statement:
--   The Column Families construction uses the qs lap row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L60-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L60-L83

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_lap_row {h : ℕ} (r : Fin (h + 1) → Fin n) (p : Fin (h + 1)) (I : Finset (Fin n)) (hI : I.card = h + 1)
    (A : Finset (Fin n)) (hA : A.card = h) (hr : ∀ i, r (p.succAbove i) = A.orderEmbOfFin hA i) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g (r p) m =
      (-1) ^ (h - (p : ℕ)) * Matrix.det (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)) := by sorry
