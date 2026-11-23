-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_gt
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_card_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:50.813502+00:00
-- url     : https://prove2.me/theorems/1650c9ce-ea05-4a11-b025-4377a09a4f49
-- title:
--   Column Families: qs card gt
-- statement:
--   The Column Families construction uses the qs card gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsMnTranspose.lean#L39-L53

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_card_gt {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1)) :
    ((s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·)).card = h - j := by sorry
