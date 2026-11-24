-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_strDown
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_strDown
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:48.780905+00:00
-- url     : https://prove2.me/theorems/b0ae8d7d-c8ba-49b5-b2c1-61c5168f2baf
-- title:
--   Column Families: qs mem str Down
-- statement:
--   The Column Families construction uses the qs mem str Down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L174-L175

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
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
variable {n : ℕ} [NeZero n]
omit [NeZero n]
open Classical

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_strDown {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b := by sorry
