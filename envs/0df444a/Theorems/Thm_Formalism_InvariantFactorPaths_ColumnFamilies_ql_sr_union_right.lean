-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_union_right
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_union_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:36.904487+00:00
-- url     : https://prove2.me/theorems/3c1a37b8-832f-4466-a2e5-3a03de1d3a29
-- title:
--   Column Families: ql sr union right
-- statement:
--   The Column Families construction uses the ql sr union right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L23-L25

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
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
variable {R : Type*} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_union_right (A : Finset (Fin n)) {B C : Finset (Fin n)} (h : Disjoint B C) :
    ql_sr R A (B ∪ C) = ql_sr R A B * ql_sr R A C := by sorry
