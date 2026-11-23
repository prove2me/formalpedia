-- Prove2me | Theorems.Thm_Formalism_REAL_self_mem_lowering_span
-- name    : Formalism.REAL.self_mem_lowering_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:14.137918+00:00
-- url     : https://prove2.me/theorems/56ff93e8-6ce4-4250-bffa-d936e0221949
-- title:
--   REAL: self mem lowering span
-- statement:
--   The REAL construction uses the self mem lowering span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L118-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L118-L118

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem Formalism.REAL.self_mem_lowering_span (x : V) : x ∈ lowSpan ε F x := by sorry
