-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_lead
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_lead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:01.925681+00:00
-- url     : https://prove2.me/theorems/6dfafed1-9347-4bec-9efd-f357e5aed61a
-- title:
--   Column Families: ql lead
-- statement:
--   The Column Families construction uses the ql lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L100-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L100-L145

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    ∃ k0 : LamIdx n b, ql_be b k0 = nu - mu ∧
      (ql_ps b mu nu (canT mu, k0) (canT nu) = 1 ∨ ql_ps b mu nu (canT mu, k0) (canT nu) = -1) := by sorry
