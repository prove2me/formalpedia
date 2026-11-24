-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_w_cast
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_w_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:23.879354+00:00
-- url     : https://prove2.me/theorems/2dbdea42-ee62-4dd6-9e94-949492c7df2a
-- title:
--   Column Families: ql w cast
-- statement:
--   The Column Families construction uses the ql w cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L60-L63

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_w_cast (A K I : Finset (Fin n)) : ((ql_w ℤ A K I : ℤ) : R) = ql_w R A K I := by sorry
