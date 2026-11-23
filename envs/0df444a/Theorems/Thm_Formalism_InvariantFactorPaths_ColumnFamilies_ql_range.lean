-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_range
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:32.525053+00:00
-- url     : https://prove2.me/theorems/5838a553-4575-4012-9a84-4e1cd13f96f3
-- title:
--   Column Families: ql range
-- statement:
--   The Column Families construction uses the ql range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L86-L90

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
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
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_range {mu nu : Fin n → ℤ} {b : ℕ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    mu (lastIdx n) + ((nu 0 - mu (lastIdx n)).toNat : ℕ) = nu 0 := by sorry
