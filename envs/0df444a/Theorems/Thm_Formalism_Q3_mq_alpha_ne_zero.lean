-- Prove2me | Theorems.Thm_Formalism_Q3_mq_alpha_ne_zero
-- name    : Formalism.Q3.mq_alpha_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:36.533814+00:00
-- url     : https://prove2.me/theorems/24f9da23-c43a-4524-8f6d-8a63fade2299
-- title:
--   Q3: mq alpha ne zero
-- statement:
--   The Q3 construction uses the mq alpha ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L14-L18

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
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
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}

theorem Formalism.Q3.mq_alpha_ne_zero (h : IsMQ a α) (ha : ∀ i, a i ≠ 0) (i : Fin k) : α i ≠ 0 := by sorry
