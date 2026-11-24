-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_cast
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_cast
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:55.857846+00:00
-- url     : https://prove2.me/theorems/a9b228d2-25a6-443e-ab6a-b6d661d226c9
-- title:
--   Column Families: ql sr cast
-- statement:
--   The Column Families construction uses the ql sr cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L50-L53

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_sr_cast (A K : Finset (Fin n)) : ((ql_sr ℤ A K : ℤ) : R) = ql_sr R A K := by sorry
