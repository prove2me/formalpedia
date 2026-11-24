-- Prove2me | Theorems.Thm_Formalism_Q3_host_not_sq
-- name    : Formalism.Q3.host_not_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:03.860252+00:00
-- url     : https://prove2.me/theorems/53dabb78-209f-4c0b-9c39-f309fe38a543
-- title:
--   Q3: host not sq
-- statement:
--   The Q3 construction uses the host not sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQKummer.lean#L163-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQKummer.lean#L163-L188

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

theorem Formalism.Q3.host_not_sq (q : Fin 3 → ℕ) (hq : Hyp3 q) (S : Finset (Fin 3)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by sorry
