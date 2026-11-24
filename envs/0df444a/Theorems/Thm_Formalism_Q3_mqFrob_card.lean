-- Prove2me | Theorems.Thm_Formalism_Q3_mqFrob_card
-- name    : Formalism.Q3.mqFrob_card
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:18.027976+00:00
-- url     : https://prove2.me/theorems/d4d0a669-713d-4afe-9aff-4c6bc81b47b2
-- title:
--   Q3: mq Frob card
-- statement:
--   The Q3 construction uses the mq Frob card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQFrob.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQFrob.lean#L15-L18

import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3

theorem Formalism.Q3.mqFrob_card {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by sorry
