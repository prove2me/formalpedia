-- Prove2me | Theorems.Thm_Formalism_REAL_compact_casimir_term_highest
-- name    : Formalism.REAL.compact_casimir_term_highest
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:10.389356+00:00
-- url     : https://prove2.me/theorems/f0e00700-b1fc-4e52-9bd9-ea078790bb85
-- title:
--   REAL: compact casimir term highest
-- statement:
--   The REAL construction uses the compact casimir term highest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L308-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L308-L321

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

theorem Formalism.REAL.compact_casimir_term_highest (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) {a b : Fin n}
    (hab : ε a = ε b) :
    F a b (F b a x) = ((if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0 : ℝ) : ℂ) • x := by sorry
