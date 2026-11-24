-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_card_of_ef_one
-- name    : Formalism.MainNotions.J.card_of_ef_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:34.444284+00:00
-- url     : https://prove2.me/theorems/32c24e64-87d7-4d4f-bb90-e27e86132cf3
-- title:
--   J: card of ef one
-- statement:
--   The J construction uses the card of ef one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L85-L89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)

theorem Formalism.MainNotions.J.card_of_ef_one (hp : p.Prime)
    (h : ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1) :
    (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K := by sorry
