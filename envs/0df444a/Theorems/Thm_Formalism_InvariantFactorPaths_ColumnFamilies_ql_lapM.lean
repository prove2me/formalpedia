-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_lapM
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_lapM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:42.777843+00:00
-- url     : https://prove2.me/theorems/034d723d-839d-486a-a68c-84d987ce0327
-- title:
--   Column Families: ql lap M
-- statement:
--   The Column Families construction uses the ql lap M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L178-L180

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
variable (g : Matrix (Fin n) (Fin n) R)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_lapM (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = ∑ I', qs_mn g I I' * ql_w R A K I' := by sorry
