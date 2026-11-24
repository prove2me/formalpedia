-- Prove2me | Theorems.Thm_Formalism_Q3_CMConjugation_not_sq_mul
-- name    : Formalism.Q3.CMConjugation.not_sq_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:00.329322+00:00
-- url     : https://prove2.me/theorems/eb7e8a98-482c-456c-a6ab-6916fed851d3
-- title:
--   CMConjugation: not sq mul
-- statement:
--   The CMConjugation construction uses the not sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L97-L105

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMConjugation
variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

theorem Formalism.Q3.CMConjugation.not_sq_mul (p m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) : ¬ IsSquare (p * m) := by sorry
