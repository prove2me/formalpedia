-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_strUp
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_strUp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:57.967808+00:00
-- url     : https://prove2.me/theorems/b51908e3-75ab-4cb3-96c2-4127383a3cd8
-- title:
--   Column Families: qs mem str Up
-- statement:
--   The Column Families construction uses the qs mem str Up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L172-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L172-L172

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_strUp {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := by sorry
