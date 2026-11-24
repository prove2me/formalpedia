-- Prove2me | Theorems.Thm_Formalism_Q3_mq_injective
-- name    : Formalism.Q3.mq_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:36.618315+00:00
-- url     : https://prove2.me/theorems/dcec7943-8edf-46f7-81a5-5973e7caca20
-- title:
--   Q3: mq injective
-- statement:
--   The Q3 construction uses the mq injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L51-L59

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

theorem Formalism.Q3.mq_injective (h : IsMQ a α) : Function.Injective (galSign α) := by sorry
