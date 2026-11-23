-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_oe_succAbove
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_oe_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:11.611137+00:00
-- url     : https://prove2.me/theorems/f33d4380-95f5-4a36-9cba-cce70b9e4fb5
-- title:
--   Column Families: qs oe succ Above
-- statement:
--   The Column Families construction uses the qs oe succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L30-L37

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_oe_succAbove {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1))
    (hs' : (s.erase (s.orderEmbOfFin hs j)).card = h) (i : Fin h) :
    s.orderEmbOfFin hs (j.succAbove i) = (s.erase (s.orderEmbOfFin hs j)).orderEmbOfFin hs' i := by sorry
