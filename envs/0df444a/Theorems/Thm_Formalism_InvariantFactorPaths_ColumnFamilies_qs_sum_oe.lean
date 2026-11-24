-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sum_oe
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_oe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:56.608222+00:00
-- url     : https://prove2.me/theorems/5bfe7e40-613f-4159-9779-3d801bcb3185
-- title:
--   Column Families: qs sum oe
-- statement:
--   The Column Families construction uses the qs sum oe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L55-L58

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_sum_oe {M : Type*} [AddCommMonoid M] {h : ℕ} (I : Finset (Fin n)) (hI : I.card = h) (f : Fin n → M) :
    ∑ m ∈ I, f m = ∑ j : Fin h, f (I.orderEmbOfFin hI j) := by sorry
