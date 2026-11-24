-- Prove2me | Theorems.Thm_Formalism_Q3_CMRootsOfUnity_no_four
-- name    : Formalism.Q3.CMRootsOfUnity.no_four
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:11.384804+00:00
-- url     : https://prove2.me/theorems/9213c293-14da-4562-b528-4fc721ed7b26
-- title:
--   CMRoots Of Unity: no four
-- statement:
--   The CMRoots Of Unity construction uses the no four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L99-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L99-L105

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}
variable {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

theorem Formalism.Q3.CMRootsOfUnity.no_four (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (η : E)
    (hη : IsPrimitiveRoot η 4) : False := by sorry
