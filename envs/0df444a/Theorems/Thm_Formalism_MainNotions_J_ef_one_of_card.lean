-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_ef_one_of_card
-- name    : Formalism.MainNotions.J.ef_one_of_card
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:10.178787+00:00
-- url     : https://prove2.me/theorems/1a6377af-e87b-4acd-89bd-8158569f1b25
-- title:
--   J: ef one of card
-- statement:
--   The J construction uses the ef one of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L74-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/SfromGLt.lean#L74-L83

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

theorem Formalism.MainNotions.J.ef_one_of_card (hp : p.Prime)
    (h : (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by sorry
