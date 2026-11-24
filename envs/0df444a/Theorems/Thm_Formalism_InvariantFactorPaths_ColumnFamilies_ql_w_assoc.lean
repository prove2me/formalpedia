-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_w_assoc
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_w_assoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:27.509827+00:00
-- url     : https://prove2.me/theorems/d13d3e67-4cca-459c-b4b8-68fa50603f1a
-- title:
--   Column Families: ql w assoc
-- statement:
--   The Column Families construction uses the ql w assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L69-L78

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_w_assoc (A B C I : Finset (Fin n)) :
    ∑ M, ql_w R A B M * ql_w R M C I = ∑ M, ql_w R B C M * ql_w R A M I := by sorry
