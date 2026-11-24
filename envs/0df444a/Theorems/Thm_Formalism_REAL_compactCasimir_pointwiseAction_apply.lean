-- Prove2me | Theorems.Thm_Formalism_REAL_compactCasimir_pointwiseAction_apply
-- name    : Formalism.REAL.compactCasimir_pointwiseAction_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:24.383867+00:00
-- url     : https://prove2.me/theorems/68373a72-c55c-4f3c-8e38-f9eddab32292
-- title:
--   REAL: compact Casimir pointwise Action apply
-- statement:
--   The REAL construction uses the compact Casimir pointwise Action apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L214-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L214-L222

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem Formalism.REAL.compactCasimir_pointwiseAction_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : CasK ε (ptE (j := j) E) F α = CasK ε E (F α) := by sorry
