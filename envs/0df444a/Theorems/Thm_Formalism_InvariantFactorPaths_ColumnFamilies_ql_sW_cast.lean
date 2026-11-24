-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sW_cast
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_sW_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:24.481122+00:00
-- url     : https://prove2.me/theorems/8daa9e0c-5bd8-4af9-abfa-68892e0ce03b
-- title:
--   Column Families: ql s W cast
-- statement:
--   The Column Families construction uses the ql s W cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LWedge.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LWedge.lean#L29-L31

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_sW_cast : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), ((ql_sW ℤ N D : ℤ) : R) = ql_sW R N D
  := by sorry
