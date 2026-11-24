-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_laplace_expansion_column
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.laplace_expansion_column
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:23.326832+00:00
-- url     : https://prove2.me/theorems/03cee21f-ec82-4baf-a311-4b5caa00c7de
-- title:
--   Column Families: laplace expansion column
-- statement:
--   The Column Families construction uses the laplace expansion column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L109-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean#L109-L123

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.laplace_expansion_column (B I : Finset (Fin n)) (m : Fin n) :
    ∑ M, ∑ k, qs_mn g M B * g k m * ql_w R M {k} I = wedgeSign R B {m} * qs_mn g I (B ∪ {m}) := by sorry
