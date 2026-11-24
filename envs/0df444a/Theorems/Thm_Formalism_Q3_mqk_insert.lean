-- Prove2me | Theorems.Thm_Formalism_Q3_mqk_insert
-- name    : Formalism.Q3.mqk_insert
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:35.185928+00:00
-- url     : https://prove2.me/theorems/591c1c2d-045a-40f3-9bda-3783d52419e9
-- title:
--   Q3: mqk insert
-- statement:
--   The Q3 construction uses the mqk insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQKummer.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQKummer.lean#L97-L103

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {E : Type*} [Field E] [CharZero E]
omit [CharZero E]

theorem Formalism.Q3.mqk_insert (F : Type*) [Field F] [Algebra F E] {k : ℕ} (α : Fin k → E) (T : Finset (Fin k)) (j : Fin k) :
    mqkField F α (insert j T) =
      (IntermediateField.adjoin (mqkField F α T) {α j}).restrictScalars F := by sorry
