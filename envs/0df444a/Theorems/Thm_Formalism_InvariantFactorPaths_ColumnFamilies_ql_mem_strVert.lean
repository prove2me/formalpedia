-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_strVert
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.ql_mem_strVert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:23.902125+00:00
-- url     : https://prove2.me/theorems/70a9e379-fd0e-4188-8a95-36504f3c8d78
-- title:
--   Column Families: ql mem str Vert
-- statement:
--   The Column Families construction uses the ql mem str Vert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean#L37-L39

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.ql_mem_strVert {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strVert mu b) :
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by sorry
