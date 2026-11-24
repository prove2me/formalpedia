-- Prove2me | Theorems.Thm_Formalism_REAL_lowering_word_raises_in_span
-- name    : Formalism.REAL.lowering_word_raises_in_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:38.271981+00:00
-- url     : https://prove2.me/theorems/52709287-c643-4205-829a-3f78baf3b26b
-- title:
--   REAL: lowering word raises in span
-- statement:
--   The REAL construction uses the lowering word raises in span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L133-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L133-L167

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

theorem Formalism.REAL.lowering_word_raises_in_span (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∀ a b, ε a = ε b → F a b (ew F w x) ∈ lowSpan ε F x := by sorry
