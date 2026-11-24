-- Prove2me | Theorems.Thm_Formalism_REAL_word_action_cons
-- name    : Formalism.REAL.word_action_cons
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:25:57.051411+00:00
-- url     : https://prove2.me/theorems/a529e0f8-d527-4d14-bd54-fc7d4d0eff2c
-- title:
--   REAL: word action cons
-- statement:
--   The REAL construction uses the word action cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L45-L46

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

theorem Formalism.REAL.word_action_cons (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (x : V) :
    ew F (p :: w) x = F p.1 p.2 (ew F w x) := by sorry
