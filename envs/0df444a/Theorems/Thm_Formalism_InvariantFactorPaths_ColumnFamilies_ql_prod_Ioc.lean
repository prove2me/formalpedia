-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_prod_Ioc
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_prod_Ioc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:34.455849+00:00
-- url     : https://prove2.me/theorems/2b037365-2754-415f-bcc6-a2be2b3a2379
-- title:
--   Column Families: ql prod Ioc
-- statement:
--   The Column Families construction uses the ql prod Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean#L14-L23

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_prod_Ioc {M : Type*} [CommMonoid M] (lo : ℤ) (N : ℕ) (φ : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo (lo + N), φ c = ∏ j : Fin N, φ (lo + 1 + (j : ℕ)) := by sorry
