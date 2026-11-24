-- Prove2me | Theorems.Thm_Formalism_REAL_lowering_span_stable
-- name    : Formalism.REAL.lowering_span_stable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:19.5568+00:00
-- url     : https://prove2.me/theorems/d2c57b9e-e371-4a7c-b4b2-fcac5c713170
-- title:
--   REAL: lowering span stable
-- statement:
--   The REAL construction uses the lowering span stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L169-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L169-L176

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

theorem Formalism.REAL.lowering_span_stable (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) :
    KStable ε F (lowSpan ε F x) := by sorry
