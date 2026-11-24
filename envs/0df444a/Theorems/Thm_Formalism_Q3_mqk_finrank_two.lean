-- Prove2me | Theorems.Thm_Formalism_Q3_mqk_finrank_two
-- name    : Formalism.Q3.mqk_finrank_two
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:43.057588+00:00
-- url     : https://prove2.me/theorems/20759763-9d84-4b1d-9cbd-65c15a3b3b26
-- title:
--   Q3: mqk finrank two
-- statement:
--   The Q3 construction uses the mqk finrank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQKummer.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQKummer.lean#L74-L85

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
variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

theorem Formalism.Q3.mqk_finrank_two (K : IntermediateField F E) (β b : E) (hb : b ∈ K) (hβ : β ^ 2 = b)
    (hns : ∀ z ∈ K, z ^ 2 ≠ b) :
    Module.finrank K (IntermediateField.adjoin K {β}) = 2 := by sorry
