-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_P_cast
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_P_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:47.472276+00:00
-- url     : https://prove2.me/theorems/b77e4591-b235-4ba3-8d86-7e9c6391f915
-- title:
--   Column Families: ql P cast
-- statement:
--   The Column Families construction uses the ql P cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LWedge.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LWedge.lean#L96-L98

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
variable (g : Matrix (Fin n) (Fin n) R)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_P_cast {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ((ql_P ℤ k L i : ℤ) : R) = ql_P R k L i := by sorry
