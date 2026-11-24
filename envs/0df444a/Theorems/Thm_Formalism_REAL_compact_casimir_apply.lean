-- Prove2me | Theorems.Thm_Formalism_REAL_compact_casimir_apply
-- name    : Formalism.REAL.compact_casimir_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:31.895324+00:00
-- url     : https://prove2.me/theorems/1f7a3fc0-f779-4861-8b1c-57193e0e942c
-- title:
--   REAL: compact casimir apply
-- statement:
--   The REAL construction uses the compact casimir apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L299-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L299-L306

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

theorem Formalism.REAL.compact_casimir_apply (y : V) :
    CasK ε F y = ∑ a, ∑ b, if ε a = ε b then F a b (F b a y) else 0 := by sorry
